(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2012 Baelde, Tiu, Ziegler, Gacek, Heath               *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

exception Level_inconsistency

exception Variable_leakage
exception Abort_search

open Format
open System
open Term

(* Internal design of the prover has two levels, Zero and One.
 * On level One, logic vars are instantiated and eigenvars are constants.
 * On level Zero, logic vars are forbidden and eigenvars can be instantiated. *)
type level = Zero | One

let assert_level_one = function
  | One -> ()
  | Zero -> raise Level_inconsistency

module Right =
  Unify.Make (struct
                let instantiatable = Logic
                let constant_like = Eigen
              end)
module Left =
  Unify.Make (struct
                let instantiatable = Eigen
                let constant_like = Constant
              end)

let debug_max_depth = -1 (* limited but global version of #debug *)
let freezing_point = ref 0
let saturation_pressure = ref 0

type temperature = Unfrozen | Frozen of int

let unify lvl a b =
  try
    (if lvl = Zero then Left.pattern_unify else Right.pattern_unify) a b ;
    true
  with
    | Unify.Error _ -> false

(* Tabling provides a way to cut some parts of the search,
 * but we should take care not to mistake shortcuts and disproving. *)

let disprovable_stack = Stack.create ()

let clear_disprovable () =
  try
    while true do
      let s,_ = Stack.pop disprovable_stack in s := Table.Unset
    done
  with Stack.Empty -> ()

exception Found
let mark_not_disprovable_until ?(included=false) d =
  try
    Stack.iter (fun (_,disprovable) ->
                  if disprovable == d then begin
                    if included then disprovable := false ;
                    raise Found
                  end else disprovable := false)
      disprovable_stack
  with Found -> ()

type 'a answer = Known of 'a | Unknown | OffTopic

let do_open_file g =
  match g with
    | [n] ->
        begin match observe n with
          | QString name ->
              begin try
                ignore (open_user_file name) ; true
              with Sys_error e ->
                Printf.eprintf
                  "fopen_out: failed opening file %S\n %s \n" name e ;
                false
              end
          | _ -> assert false
        end
    | _ -> false

let do_close_file g =
  match g with
    | [n] ->
        begin match observe n with
          | QString name ->
              begin try
                close_user_file name ; true
              with Sys_error e ->
                Printf.eprintf
                  "fclose_out: failed closing file %S\n %s \n" name e ;
                false
              end
          | _ -> assert false
        end
    | _ -> false

let do_fprint print_fun goals =
  begin match goals with
    | h::l ->
        begin match observe h with
          | QString name ->
              begin try
                let f = get_user_file name in
                let fmt = formatter_of_out_channel f in
                List.iter (print_fun fmt) l ;
                true
              with
                | Not_found -> false
              end
          | _ -> assert false
        end
    | _ -> false
  end


(* Attempt to prove the goal [(nabla x_1..x_local . g)(S)] by
 * destructively instantiating it,
 * calling [success] on every success, and finishing with [failure]
 * which can be seen as a more usual continuation, typically
 * restoring modifications and backtracking.
 * [timestamp] must be the oldest timestamp in the goal. *)
let rec prove temperatures depth ~success ~failure ~level ~timestamp ~local g =

  if check_interrupt () then begin
    clear_disprovable () ;
    raise Interrupt
  end ;

  let g = Norm.hnorm g in
  let invalid_goal () =
    failwith (sprintf "Invalid goal %s" (Pprint.term_to_string_full [] [] g))
  in

  (* Function to prove _distinct predicate *)
  let prove_distinct goals =
    let sol = ref [] in
    let match_list l1 l2 = List.for_all2 eq l1 l2 in
    let a = match goals with [a] -> a | _ -> invalid_goal () in
    let a = Norm.deep_norm a in
    let vars = if level = Zero then eigen_vars [a] else logic_vars [a] in
    prove temperatures (depth+1) ~level ~timestamp ~failure ~local a
      ~success:(fun ts k ->
                  let tm_list = List.map shared_copy vars in
                  if List.exists (match_list tm_list) !sol then k () else begin
                    sol := tm_list :: !sol ;
                    success ts k
                  end)
  in

  (* Function to prove _abstract predicate *)
  let prove_abstract goals =
    let a,b,c = match goals with [a;b;c] -> a,b,c | _ -> invalid_goal () in
    let a = Norm.deep_norm a in
    let b = Norm.deep_norm b in
    let c = Norm.deep_norm c in
    let vars =
      if level = Zero then eigen_vars [a] else logic_vars [a]
    in
    let d =
      List.fold_left (fun t v -> app b [abstract_flex v t]) a vars
    in
    let g = op_eq c d in
    prove temperatures (depth+1) ~level ~success ~failure ~timestamp ~local g
  in

  (* Function to prove _not predicate *)
  let prove_not goals =
    let a = match goals with [a] -> a | _ -> invalid_goal () in
    let a = Norm.deep_norm a in
    let state = save_state () in
    prove temperatures (depth+1) ~level ~timestamp ~local a
      ~success:(fun ts k ->
                  restore_state state ;
                  failure ())
      ~failure:(fun () ->
                restore_state state ;
                success timestamp failure )
  in

  (* Function to prove _if predicate *)
  let prove_ite goals =
    let (a,b,c) = match goals with [a;b;c] -> a,b,c | _ -> invalid_goal () in
    let a = Norm.deep_norm a in
    let b = Norm.deep_norm b in
    let c = Norm.deep_norm c in
    let succeeded = ref false in
    let state = save_state () in
    prove temperatures (depth+1) ~level ~timestamp ~local a
      ~success:(fun ts k ->
                  (*  restore_state state ; *)
                  (*  prove temperatures (depth+1) ~success ~failure ~level
                   *  ~timestamp ~local (op_and a b) *)
                  succeeded := true ;
                  prove temperatures (depth+1) ~success ~level
                    ~timestamp:ts ~local b ~failure:k)
      (* (fun () -> restore_state state ; failure()) *)
      ~failure:(fun () ->
                  restore_state state ;
                  if !succeeded then failure () else
                    prove temperatures (depth+1) ~success ~failure
                      ~level ~timestamp ~local c)
  in

  (* 2-step procedure (table, definition)
   * to prove a predicative atom *)
  let prove_atom d args (v,temperature,temperatures) =
    if !debug || depth<=debug_max_depth then
      eprintf "[%s] Proving %a...@."
        (match temperature with Frozen t -> string_of_int t | _ -> "+")
        Pprint.pp_term g ;
    let arity = List.length args in
    let flavour,body,theorem,table,_ = get_def ~check_arity:arity d in
    (* first step, first sub-step: look at the table
     * (whether the atom is frozen or not is irrelevent at this point) *)
    let table_add,status =
      match table with
        | None -> ignore,OffTopic
        | Some table ->
            try
              let add,found,_ =
                Table.access ~allow_eigenvar:(level=One) table args
              in
              match found with
                | Some {contents=c} -> add,Known c
                | None -> add,Unknown
            with
              | Index.Cannot_table -> ignore,OffTopic
    in
    match status with
      | OffTopic ->
          prove temperatures (depth+1) ~level ~timestamp ~local ~success ~failure
            (app body args)
      | Known Table.Proved ->
          if !debug || depth<=debug_max_depth then
            eprintf "Goal (%a) proved using table@." Pprint.pp_term g;
          success timestamp failure
      | Known Table.Disproved ->
          if !debug || depth<=debug_max_depth then
            eprintf "Known disproved@." ;
          failure ()
      | Known (Table.Working disprovable) ->
          begin match temperature with
            | Frozen t ->
                (* Unfortunately, a theorem is not a clause
                 * that we can add to a definition,
                 * since it doesn't respect the flavour (e.g. the
                 * predicate notxwins from tictactoe.def involves no loop,
                 * and thus can be marked inductive as well as coinductive,
                 * whereas its theorem notxwins_symetries has loops
                 * from which we can conclude nothing).
                 * Therefore no atom is disprovable. *)
                mark_not_disprovable_until ~included:true disprovable ;
                failure ()
            | Unfrozen ->
                if flavour = CoInductive then
                  success timestamp failure
                else begin
                  (* XXX Why exactly are the intermediate atoms not disproved? *)
                  mark_not_disprovable_until disprovable ;
                  failure ()
                end
          end
      | Unknown
      | Known Table.Unset ->
          (* This handles the cases where nothing is in the table,
           * or Unset has been left, in which case the [Table.add]
           * will overwrite it. *)
          let prove body success failure temperatures =
            let table = match table with Some t -> t | None -> assert false in
            let disprovable = ref true in
            let status = ref (Table.Working disprovable) in
            let s0 = save_state () in
            let table_update_success ts k =
              ignore (Stack.pop disprovable_stack) ;
              status := Table.Proved ;
              (* TODO check that optimization: since we know that
               * there is at most one success, we ignore
               * the continuation [k] and directly jump to the
               * [failure] continuation. It _seems_ OK regarding the
               * cleanup handlers, which are just jumps to
               * previous states.
               * It is actually quite useful in examples/graph-alt.def. *)
              let k () = success ts (fun () -> restore_state s0 ; failure ()) in
              (* XXX Here be the Forward-Chaining XXX *)
              let saturate =
                match temperature with
                  | Frozen _ ->
                      (* XXX for now we don't forward-chain during backward chaining;
                       * if someday we do, we must skip "Working _"
                       * instead of failing on it *)
                      fun k -> k ()
                  | Unfrozen ->
                      (* [theorem] corresponds to the fact
                       * "forall X, theorem X -> p X" *)
                      let vars =
                        let rec aux l = function
                          | n when n <= 0 -> l
                          | n -> aux ((fresh ~lts:local Eigen ~ts:(timestamp + n))::l) (n-1)
                        in
                        aux [] arity
                      in
                      let timestamp = timestamp + arity in
                      let th_body = app theorem vars in
                      (* [store_subst] is nearly the same as for Arrow *)
                      let substs = ref [] in
                      let state = save_state () in
                      let store_subst ts k =
                        (* XXX check_variables? *)
                        substs := (get_subst state)::!substs ;
                        k ()
                      in
                      (* [make_copies] is nearly the same as for Arrow *)
                      let make_copies vs =
                        List.map
                          (fun sigma ->
                             let unsig = apply_subst sigma in
                             let newvars = List.map shared_copy vars in
                             undo_subst unsig ;
                             newvars)
                          vs
                      in
                      let rec fc k pressure = function
                        | [] -> k ()
                        | args::copies ->
                            if !debug || depth<=debug_max_depth then
                              eprintf "(%d) Tabling %a...@."
                                pressure
                                Pprint.pp_term (app d args);
                            let k () = fc k pressure copies in
                            let table_add,status =
                              try
                                let add,found,_ =
                                  Table.access ~allow_eigenvar:(level=One) table args
                                in
                                match found with
                                  | Some {contents=c} -> add,Known c
                                  | None -> add,Unknown
                              with
                                | Index.Cannot_table -> ignore,OffTopic
                            in
                            match status with
                              | OffTopic -> k ()
                              | Known Table.Proved ->
                                  if !debug || depth<=debug_max_depth then
                                    eprintf
                                      "Goal (%a) already proved!@."
                                      Pprint.pp_term (app d args);
                                  k ()
                              | Known Table.Disproved ->
                                  failwith "did our theorem just prove false?"
                              | Known (Table.Working _) -> assert false
                              | Unknown
                              | Known Table.Unset ->
                                  let status = ref Table.Proved in
                                  (* XXX allow_eigenvar? *)
                                  begin try table_add status
                                  with Index.Cannot_table -> assert false end ;
                                  if !debug || depth<=debug_max_depth then
                                    eprintf
                                      "Goal (%a) proved using forward chaining@."
                                      Pprint.pp_term (app d args) ;
                                  aux args k pressure
                      and aux args k = function
                        | pressure when pressure < !saturation_pressure ->
                            (* TODO replace this DFS by a BFS
                             * (or at least try whether it's more efficient
                             * memory-wise) *)
                            let failure () =
                              let copies = make_copies !substs in
                              substs := [] ;
                              fc k ((pressure+1)) copies
                            in
                            (* XXX for now we don't backward-chain during forward chaining;
                             * we must also use [args] at least once
                             * to improve performance *)
                            prove ((v,Frozen 0)::temperatures) (depth+1) ~local ~timestamp
                              ~level:Zero ~success:store_subst ~failure th_body
                        | pressure when !saturation_pressure < 0 ->
                            let failure () =
                              let copies = make_copies !substs in
                              substs := [] ;
                              fc k pressure copies
                            in
                            prove ((v,Frozen 0)::temperatures) (depth+1) ~local ~timestamp
                              ~level:Zero ~success:store_subst ~failure th_body
                        | _ -> k ()
                      in
                      fun k -> aux args k 0
              in
              (* XXX There was the Forward-Chaining XXX *)
              saturate k
            in
            let table_update_failure () =
              begin match !status with
                | Table.Proved ->
                    (* This is just backtracking, we are seeing the tabling
                     * entry corresponding to a previous goal.
                     * Never happens if we skipped the success continuation. *)
                    assert false
                | Table.Working _ ->
                    ignore (Stack.pop disprovable_stack) ;
                    if !disprovable then begin
                      status := Table.Disproved ;
                    end else
                      status := Table.Unset
                | Table.Disproved | Table.Unset -> assert false
              end ;
              failure ()
            in
            if try
              table_add status ;
              true
            with Index.Cannot_table -> false
            then begin
              Stack.push (status,disprovable) disprovable_stack ;
              prove temperatures (depth+1) ~level ~local ~timestamp
                ~success:table_update_success
                ~failure:table_update_failure
                (app body args)
            end else
              prove temperatures (depth+1) ~level ~local ~success ~failure
                ~timestamp (app body args)
          in
          (* first step, second sub-step: freeze the atom if needed,
           * unfold the theorem *)
          let temp,success,failure =
            match temperature with
              | Frozen t ->
                  t,
                  (fun timestamp failure ->
                     if !debug || depth<=debug_max_depth then
                       eprintf
                         "Frozen goal (%a) proved using backward chaining@."
                         Pprint.pp_term g;
                     success timestamp failure),
                  failure
              | Unfrozen ->
                  !freezing_point,
                  (fun timestamp failure ->
                     if !debug || depth<=debug_max_depth then
                       eprintf
                         "Unfrozen goal (%a) proved using backward chaining@."
                         Pprint.pp_term g;
                     success timestamp failure),
                  (* second step: unfreeze the atom,
                   * unfold the definition *)
                  (fun () -> prove body success failure temperatures)
          in
          if temp > 0 then
            prove theorem success failure ((v,Frozen (temp-1))::temperatures)
          else if temp = 0 then
            failure ()
          else
            prove theorem success failure ((v,Frozen (-1))::temperatures)
  in

  match observe g with
    | True -> success timestamp failure
    | False -> failure ()

    (* Abort search: throw an exception *)
    | Var v when v == Logic.var_abort_search ->  raise Abort_search

    | Var v ->
        let temperature,temperatures =
          try List.assq v temperatures,List.remove_assq v temperatures
          with Not_found -> Unfrozen,temperatures
        in
        prove_atom g [] (v,temperature,temperatures)

    (* Solving an equality *)
    | Binop (Eq,t1,t2) ->
        let state = save_state () in
        let failure () = restore_state state ; failure () in
        if unify level (Norm.hnorm t1) (Norm.hnorm t2) then
          success timestamp failure
        else
          failure ()

    (* Proving a conjunction *)
    | Binop (And,t1,t2) ->
        let rec conj ts failure = function
          | [] -> success ts failure
          | goal::goals ->
              prove temperatures (depth+1)
                ~local ~level ~timestamp
                ~success:(fun ts' k -> conj (max ts ts') k goals)
                ~failure
                goal
        in
        conj timestamp failure [Norm.hnorm t1;Norm.hnorm t2]

    (* Proving a disjunction *)
    | Binop (Or,t1,t2) ->
        let rec alt = function
          | [] -> failure ()
          | g::goals ->
              prove temperatures (depth+1)
                ~level ~local ~success ~timestamp
                ~failure:(fun () -> alt goals)
                g
        in
        alt [Norm.hnorm t1;Norm.hnorm t2]

    (* Level 1: Implication *)
    | Binop (Arrow,a,b) ->
        assert_level_one level ;
        let a = Norm.deep_norm a in
        let b = Norm.deep_norm b in
        let check_variables =
          let eigen = eigen_vars [a] in
          let logic = logic_vars [b] in
          let var v =
            match observe v with
              | Var v -> v
              | _ -> assert false
          in
          let max = (* maximum logic variable timestamp *)
            List.fold_left
              (fun m v -> max m (var v).ts) (-1) logic
          in
          let eigen = List.filter (fun v -> (var v).ts <= max) eigen in
          (* Check that all eigen-variables on which logic vars
           * can depend are instantiated to distinct eigenvars.
           * Then LLambda unifications will be preserved. *)
          let var v =
            match observe v with
              | Var v when v.tag = Eigen -> v
              | _ -> assert false
              (* XXX should probably be
               * "raise (Unify.NotLLambda v)",
               * but can we find an example of failure? *)
          in
          fun () ->
            (* This is called when some left solution has been
             * found. We check that everything is a variable. *)
            let eigen = List.map (fun v -> v,var v) eigen in
            let rec unicity = function
              | [] -> ()
              | (va,a)::tl ->
                  (* TODO this doesn't need to be checked in that order,
                   * so make it tail-rec *)
                  if List.exists (fun (_,b) -> a=b) tl then
                    raise (Unify.NotLLambda va) ;
                  unicity tl
            in
            unicity eigen
        in
        (* Solve [a] using level 0,
         * remind of the solution substitutions as slices of the bind stack,
         * then prove [b] at level 1 for every solution for [a],
         * thanks to the commutability between patches for [a] and [b],
         * one modifying eigenvars,
         * the other modifying logical variables. *)
        let substs = ref [] in
        let state = save_state () in
        let store_subst ts k =
          check_variables () ;
          (* We get sigma by comparing the current solution
           * with the state [k] will leave the system in,
           * and we store it. *)
          substs := (ts,get_subst state)::!substs ;
          k ()
        in
        let make_copies vs g =
          List.map
            (fun (ts,sigma) ->
               let unsig = apply_subst sigma in
               let newg = shared_copy g in
               undo_subst unsig ;
               (ts, newg))
            vs
        in
        let rec prove_conj ts failure = function
          | [] -> success ts failure
          | (ts'',g)::gs ->
              prove temperatures (depth+1) ~level ~local ~timestamp:ts''
                ~success:(fun ts' k -> prove_conj (max ts ts') k gs)
                ~failure g
        in
        prove temperatures (depth+1) ~level:Zero ~local ~timestamp a
          ~success:store_subst
          ~failure:(fun () ->
                      prove_conj timestamp failure (make_copies !substs b))

    (* Level 1: Universal quantification *)
    | Binder (Forall,n,goal) ->
        assert_level_one level ;
        let goal = lambda n goal in
        let vars =
          let rec aux l = function
            | n when n <= 0 -> l
            | n -> aux ((fresh ~lts:local Eigen ~ts:(timestamp + n))::l) (n-1)
          in
          aux [] n
        in
        let goal = app goal vars in
        prove temperatures (depth+1) ~local ~timestamp:(timestamp + n) ~level
          ~success ~failure goal

    (* Local quantification *)
    | Binder (Nabla,n,goal) ->
        let goal = lambda n goal in
        let vars =
          let rec aux l = function
            | n when n <= 0 -> l
            | n -> aux ((nabla (local + n))::l) (n-1)
          in
          aux [] n
        in
        let goal = app goal vars in
        prove temperatures (depth+1) ~local:(local + n) ~timestamp ~level
          ~success ~failure goal

    (* Existential quantification *)
    | Binder (Exists,n,goal) ->
        let goal = lambda n goal in
        let timestamp,vars = match level with
          | Zero ->
              let rec aux l = function
                | n when n <= 0 -> l
                | n -> aux ((fresh ~lts:local Eigen ~ts:(timestamp + n))::l) (n-1)
              in
              timestamp + n,aux [] n
          | One ->
              let rec aux l = function
                | n when n <= 0 -> l
                | n -> aux ((fresh ~lts:local Logic ~ts:timestamp)::l) (n-1)
              in
              timestamp,aux [] n
        in
        let goal = app goal vars in
        prove temperatures (depth+1) ~local ~timestamp ~level
          ~success ~failure goal

    | App (hd,goals) ->
        let goals = List.map Norm.hnorm goals in
        begin match observe hd with
          (* Checking equivariance between terms *)
          | Var v when v == Logic.var_check_eqvt ->
              let a,b = match goals with [a;b] -> a,b | _ -> invalid_goal () in
              let a = Norm.deep_norm a in
              let b = Norm.deep_norm b in
              if (eqvt a b) then success timestamp failure else failure ()

          (* Proving a negation-as-failure *)
          | Var v when v == Logic.var_not ->
              prove_not goals

          (* Proving if-then-else *)
          | Var v when v == Logic.var_ite ->
              prove_ite goals

          (* Proving abstract-predicate *)
          | Var v when v == Logic.var_abspred ->
              prove_abstract goals

          (* Checking rigidity assumption *)
          | Var v when v == Logic.var_assert_rigid ->
             let a = match goals with [a] -> a | _ -> invalid_goal () in
             let a = Norm.deep_norm a in
             let vars = if level = Zero then eigen_vars [a] else logic_vars [a] in
             begin match vars with
               | [] -> success timestamp failure
               | _ -> raise Variable_leakage
             end

          (* proving cut predicate *)
          | Var v when v == Logic.var_cutpred ->
             let a = match goals with [a] -> a | _ -> invalid_goal () in
             let a = Norm.deep_norm a in
             let state = save_state () in
             prove temperatures (depth+1) ~level ~local ~timestamp ~failure a
               ~success:(fun ts k -> success ts (fun () -> restore_state state ; failure ()) )

          (* Proving distinct-predicate *)
          | Var v when v == Logic.var_distinct ->
              prove_distinct goals

          (* Output *)
          | Var v when v == Logic.var_print ->
              List.iter (fun t -> printf "%a%!" Pprint.pp_term t) goals ;
              success timestamp failure

          | Var v when v == Logic.var_println ->
              List.iter (fun t -> printf "%a@." Pprint.pp_term t) goals ;
              success timestamp failure

          | Var v when v == Logic.var_printstr ->
              List.iter (fun t -> match observe t with
                           | QString s -> printf "%s%!" s
                           | _ -> failwith "an actual quoted string is needed by printstr")
                goals ;
              success timestamp failure

          | Var v when v == Logic.var_fprint ->
              let print_fun fmt t =
                fprintf fmt "%a%!" Pprint.pp_term t
              in
              if do_fprint print_fun goals then success timestamp failure
              else failure ()

          | Var v when v == Logic.var_fprintln ->
              let print_fun fmt t =
                fprintf fmt "%a@." Pprint.pp_term t
              in
              if do_fprint print_fun goals then success timestamp failure
              else failure ()

          | Var v when v == Logic.var_fprintstr ->
              let print_fun fmt t = match observe t with
                | QString s -> fprintf fmt "%s%!" s
                | _ -> failwith "an actual quoted string is needed by fprintstr"
              in
              if do_fprint print_fun goals then success timestamp failure
              else failure ()

          (* Opening file for output *)
          | Var v when v == Logic.var_fopen_out ->
              assert_level_one level ;
              if (do_open_file goals) then success timestamp failure
              else failure ()

          | Var v when v == Logic.var_fclose_out ->
              assert_level_one level ;
              if (do_close_file goals) then success timestamp failure
              else failure ()

          (* Check for definitions *)
          | Var v ->
              let temperature,temperatures =
                try List.assq v temperatures,List.remove_assq v temperatures
                with Not_found -> Unfrozen,temperatures
              in
              prove_atom hd goals (v,temperature,temperatures)

          (* Invalid goal *)
          | _ -> invalid_goal ()
        end

    (* Failure *)
    | _ -> invalid_goal ()

(* Wrap prove with sanity checks. *)
let prove ~success ~failure ~level ~timestamp ~local g =
  let s0 = save_state () in
  let success ts k =
    assert (Stack.is_empty disprovable_stack) ;
    success ts k
  in
  let failure () =
    assert (Stack.is_empty disprovable_stack) ;
    assert (s0 = save_state ()) ;
    failure ()
  in
  try
    prove [] 0 ~success ~failure ~level ~timestamp ~local g
  with e ->
    clear_disprovable () ;
    restore_state s0 ;
    raise e

let toplevel_prove g =
  let s0 = save_state () in
  let vars = List.map (fun t -> Pprint.term_to_string t, t)
               (List.rev (logic_vars [g])) in
  let found = ref false in
  let reset,time =
    let t0 = ref (Unix.gettimeofday ()) in
      (fun () -> t0 := Unix.gettimeofday ()),
      (fun () ->
         if !time then
           printf "+ %.0fms@." (1000. *. (Unix.gettimeofday () -. !t0)))
  in
  let show _ k =
    time () ;
    found := true ;
    if vars = [] then printf "Yes.@." else
      printf "Solution found:@." ;
    List.iter
      (fun (o,t) -> printf " %s = %a@." o Pprint.pp_term t)
      vars ;
    printf "More [y] ? %!" ;
    let l = input_line stdin in
    if l = "" || l.[0] = 'y' || l.[0] = 'Y' then begin
      reset () ;
      k ()
    end else begin
      restore_state s0 ;
      printf "Search stopped.@."
    end
  in
  prove ~level:One ~local:0 ~timestamp:0 g
    ~success:show
    ~failure:(fun () ->
                time () ;
                if !found then printf "No more solutions.@."
                else printf "No.@.")
