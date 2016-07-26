(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2012 Baelde, Tiu, Ziegler, Heath                      *)
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

module Logic =
struct
  let not               = Term.atom ~tag:Term.Constant "_not"
  let ite               = Term.atom ~tag:Term.Constant "_if"
  let abspred           = Term.atom ~tag:Term.Constant "_abstract"
  let distinct          = Term.atom ~tag:Term.Constant "_distinct"
  let assert_rigid      = Term.atom ~tag:Term.Constant "_rigid"
  let abort_search      = Term.atom ~tag:Term.Constant "_abort"
  let cutpred           = Term.atom ~tag:Term.Constant "_cut"
  let check_eqvt        = Term.atom ~tag:Term.Constant "_eqvt"

  let print             = Term.atom ~tag:Term.Constant "print"
  let println           = Term.atom ~tag:Term.Constant "println"
  let printstr          = Term.atom ~tag:Term.Constant "printstr"
  let fprint            = Term.atom ~tag:Term.Constant "fprint"
  let fprintln          = Term.atom ~tag:Term.Constant "fprintln"
  let fprintstr         = Term.atom ~tag:Term.Constant "fprintstr"
  let fopen_out         = Term.atom ~tag:Term.Constant "fopen_out"
  let fclose_out        = Term.atom ~tag:Term.Constant "fclose_out"


  let var_not           = Term.get_var not
  let var_ite           = Term.get_var ite
  let var_abspred       = Term.get_var abspred
  let var_distinct      = Term.get_var distinct
  let var_assert_rigid  = Term.get_var assert_rigid
  let var_abort_search  = Term.get_var abort_search
  let var_cutpred       = Term.get_var cutpred
  let var_check_eqvt    = Term.get_var check_eqvt

  let var_print         = Term.get_var print
  let var_println       = Term.get_var println
  let var_printstr      = Term.get_var printstr
  let var_fprint        = Term.get_var fprint
  let var_fprintln      = Term.get_var fprintln
  let var_fprintstr     = Term.get_var fprintstr
  let var_fopen_out     = Term.get_var fopen_out
  let var_fclose_out    = Term.get_var fclose_out


  let predefined = [ var_not ; var_ite ; var_abspred ; var_distinct ;
                     var_assert_rigid ; var_abort_search ; var_cutpred ;
                     var_check_eqvt ;
                     var_print ; var_println ; var_printstr ;
                     var_fprint ; var_fprintln ; var_fprintstr ;
                     var_fopen_out ; var_fclose_out ]
end

let debug = ref false
let time  = ref false

(* list of open files *)
let user_files : (string, out_channel) Hashtbl.t =
  Hashtbl.create 50

let reset_user_files () = Hashtbl.clear user_files

let close_all_files () =
  Hashtbl.iter
    (fun n c ->
       try close_out c with | Sys_error e -> () )
    user_files ;
  reset_user_files ()

let close_user_file name =
  try
    let f = Hashtbl.find user_files name in
    close_out f ;
    Hashtbl.remove user_files name
  with
    | Sys_error _ -> Hashtbl.remove user_files name
    | _ -> ()

let get_user_file name =
  Hashtbl.find user_files name

let open_user_file name =
  try
    Hashtbl.find user_files name
  with Not_found ->
    begin
      let fout = open_out_gen [Open_wronly;Open_creat;Open_excl] 0o600 name in
      ignore (Hashtbl.add user_files name fout) ;
      fout
    end

open Input

(* Types declarations *)

exception Invalid_type_declaration of string * Typing.pos * Typing.ki * string


let type_kinds : (Term.var,Typing.ki) Hashtbl.t =
  Hashtbl.create 100

let declare_type (p,name) ki =
  let ty_var = Term.get_var (Term.atom ~tag:Term.Constant name) in
  if Hashtbl.mem type_kinds ty_var
  then raise (Invalid_type_declaration (name,p,ki,"type already declared"))
  else Hashtbl.add type_kinds ty_var ki 
    (* match ki with *)
    (* | ki when ki = Typing.ktype -> *)
    (*     Hashtbl.add type_kinds ty_var ki *)
    (* | _ -> *)
    (*     raise (Invalid_type_declaration (name,p,ki,"no type operators yet")) *)


(* constants and predicates declarations *)

type flavour = Normal | Inductive | CoInductive

exception Missing_type of string * Typing.pos
exception Invalid_const_declaration of string * Typing.pos * Typing.ty * string
exception Invalid_flavour of string * Typing.pos * flavour * flavour
exception Invalid_pred_declaration of string * Typing.pos * Typing.ty * string
exception Invalid_bound_declaration of string * Typing.pos * Typing.ty * string


let string_of_flavour = function
  | Normal -> "Normal"
  | Inductive -> "Inductive"
  | CoInductive -> "CoInductive"

let atomic_kind (p,name) =
    let type_var = Term.get_var (Term.atom ~tag:Term.Constant name) in
    try Hashtbl.find type_kinds type_var
    with Not_found -> raise (Missing_type (name,p))

let kind_check ?(expected_kind=Typing.ktype) ty =
  (* let atomic_kind (p,name) = *)
  (*    let type_var = Term.get_var (Term.atom ~tag:Term.Constant name) in *)
  (*    try Hashtbl.find type_kinds type_var *)
  (*    with Not_found -> raise (Missing_type (name,p)) *)
  (* in *)
  Typing.kind_check ty expected_kind ~atomic_kind

type object_declaration =
  | Constant of Typing.ty
  | Predicate of (flavour*Term.term option*Term.term option*Table.t option*Typing.ty)

let defs : (Term.var,object_declaration) Hashtbl.t =
    Hashtbl.create 100

let declare_const (p,name) ty =
  let const_var = Term.get_var (Term.atom ~tag:Term.Constant name) in
  if Hashtbl.mem defs const_var
  then raise (Invalid_const_declaration
                (name,p,ty,"name conflict"))
  else if List.mem const_var Logic.predefined
  then raise (Invalid_const_declaration
                (name,p,ty,"name conflict with a predefined predicate"))
  else let _ = kind_check ty in
  Hashtbl.add defs const_var (Constant ty)

let create_def (new_predicates,global_flavour) (flavour,p,name,ty) =
  let flavour = match flavour with
    | Input.Normal -> Normal
    | Input.Inductive -> Inductive
    | Input.CoInductive -> CoInductive
  in
  let global_flavour = match global_flavour,flavour with
    | Normal,_ -> flavour
    | _,Normal -> global_flavour
    | _ when global_flavour=flavour -> flavour
    | _ -> raise (Invalid_flavour
                    (name,p,global_flavour,flavour))
  in
  let new_predicate =
    let head_var = Term.get_var (Term.atom ~tag:Term.Constant name) in
    if Hashtbl.mem defs head_var
    then raise (Invalid_pred_declaration
                  (name,p,ty,"name conflict"))
    else if List.mem head_var Logic.predefined
    then raise (Invalid_pred_declaration
                  (name,p,ty,"name conflict with a predefined predicate"))
    else let (flex,_,propositional,_) = kind_check ty in
    if not (propositional || flex) then
      raise (Invalid_pred_declaration
               (name,p,ty,Format.sprintf
                            "target type can only be %s"
                            (Typing.type_to_string Typing.tprop)))
    else begin
      let t = (if flavour=Normal then None else Some (Table.create ())) in
      Hashtbl.add defs head_var (Predicate (flavour, None, None, t, ty)) ;
      head_var,ty
    end
  in
  (new_predicate::new_predicates),global_flavour

let declare_preds decls =
  let new_predicates,_ = List.fold_left create_def ([],Normal) decls in
  new_predicates


(* typechecking, predicates definitions *)

exception Missing_declaration of string * Typing.pos option
exception Inconsistent_definition of string * Typing.pos * string


let translate_term
      ?(phead_name=None)
      ?(free_args=[])
      ?(infer=true)
      ?(expected_type=Typing.tprop)
      pre_term
      free_types =
  let iter_free_types f =
    (* XXX [QH] yeah, reading-clearing-filling a hashtable is not elegant,
     * but it is not safe to use Hashtbl.replace *during* the Hashtbl.iter,
     * I don't want the unifier to leak from Typing,
     * I don't want to build a new hashtable and to return it
     * nor to have a hashtable of references (what good is a mutable structure
     * if we don't mutate it?), so this will do until all the hashtables from System
     * are replaced with maps (or not) *)
    let l = Hashtbl.fold (fun v ty l -> (v,ty)::l) free_types [] in
    Hashtbl.clear free_types ;
    List.iter (fun (v,ty) -> Hashtbl.add free_types v (f v ty)) l
  in
  (* return (and create if needed) a typed variable
   * corresponding to the name of a free variable *)
  let typed_free_var (_,name) =
    let was_free = Term.is_free name in
    let t = Term.atom ~tag:Term.Logic name in
    let v = Term.get_var t in
    try
      let ty = Hashtbl.find free_types v in
        t,ty
    with Not_found ->
      let t,v =
        if was_free then t,v else begin
          Term.free name ;
          (* XXX in case we actually use this variable on day,
           * we should depend on the level to create an instantiable variable,
           * ie not always a Logic one (cf [mk_clause])*)
          let t = Term.atom ~tag:Term.Logic name in
          let v = Term.get_var t in
          t,v
        end
      in
      let ty = Typing.fresh_typaram () in
      Hashtbl.add free_types v ty ;
      t,ty
  in
  (* return a typed variable corresponding to the name
   * of a constant (predefined or not) or a predicate *)
  let typed_declared_var (p,name) =
    let t = Term.atom ~tag:Term.Constant name in
    let v = Term.get_var t in
    try begin
      match Hashtbl.find defs v with
        | Constant ty -> t,ty
        | Predicate (_,_,_,_,ty) -> t,ty
    end with Not_found ->
      let ty = match v with
        | v when v = Logic.var_print ->
            let ty = Typing.fresh_typaram () in
            Typing.ty_arrow [ty] Typing.tprop
        | v when v = Logic.var_println ->
            let ty = Typing.fresh_typaram () in
            Typing.ty_arrow [ty] Typing.tprop
        | v when v = Logic.var_printstr ->
            Typing.ty_arrow [Typing.tstring] Typing.tprop
        | v when v = Logic.var_fprint ->
            let ty = Typing.fresh_typaram () in
            Typing.ty_arrow [Typing.tstring;ty] Typing.tprop
        | v when v = Logic.var_fprintln ->
            let ty = Typing.fresh_typaram () in
            Typing.ty_arrow [Typing.tstring;ty] Typing.tprop
        | v when v = Logic.var_fprintstr ->
            Typing.ty_arrow [Typing.tstring;Typing.tstring] Typing.tprop
        | v when v = Logic.var_fopen_out ->
            Typing.ty_arrow [Typing.tstring] Typing.tprop
        | v when v = Logic.var_fclose_out ->
            Typing.ty_arrow [Typing.tstring] Typing.tprop
        | _ ->
            Term.free name ;
            raise (Missing_declaration (name,Some p))
      in t,ty
  in
  (* return a typed variable corresponding to the name
   * of an internal constant *)
  (* TODO regroup the following code and the one on prover.ml,
   * so that internal predicates are declared/defined in one single place *)
  let typed_intern_var (p,name) =
    let t = Term.atom ~tag:Term.Constant name in
    let v = Term.get_var t in
    let ty = match v with
      | v when v = Logic.var_not ->
          Typing.ty_arrow [Typing.tprop] Typing.tprop
      | v when v = Logic.var_ite ->
          Typing.ty_arrow [Typing.tprop;Typing.tprop;Typing.tprop] Typing.tprop
      | v when v = Logic.var_abspred ->
          let ty1 = Typing.fresh_typaram () in
          let ty2 = Typing.ty_arrow [Typing.fresh_typaram ()] ty1 in
          let ty3 = Typing.ty_arrow [ty2] ty1 in
          Typing.ty_arrow [ty1;ty3;ty1] Typing.tprop
      | v when v = Logic.var_distinct ->
          Typing.ty_arrow [Typing.tprop] Typing.tprop
      | v when v = Logic.var_assert_rigid ->
          let ty = Typing.fresh_typaram () in
          Typing.ty_arrow [ty] Typing.tprop
      | v when v = Logic.var_abort_search ->
          Typing.tprop
      | v when v = Logic.var_cutpred ->
          Typing.ty_arrow [Typing.tprop] Typing.tprop
      | v when v = Logic.var_check_eqvt ->
          let ty = Typing.fresh_typaram () in
          Typing.ty_arrow [ty;ty] Typing.tprop
      | _ ->
          Term.free name ;
          raise (Missing_declaration (name,Some p))
    in t,ty
  in
  (* return the type of the variable corresponding to an annotated ID *)
  let bound_var_type (p,name,ty) =
    let _ = kind_check ty in ty
  in
  Input.type_check_and_translate
    ~phead_name
    ~infer
    ~iter_free_types
    ~free_args
    pre_term
    expected_type
    (typed_free_var,typed_declared_var,typed_intern_var,bound_var_type,atomic_kind)

let translate_query pre_term =
  let free_types : (Term.var,Typing.ty) Hashtbl.t =
    Hashtbl.create 10
  in
  let term,_ = translate_term pre_term free_types in term

(* Replace the params by fresh variables and
 * put the constraints on the parameters in the body:
 *     pred [params] := body
 *     d X X (f X Y) := g X Y Z
 * --> d X U V       := (U = X) /\ ((V = (f X Y)) /\ (g X Y Z))
 * --> d X U V       := forall Z Y, (U = X) /\ ((V = (f X Y)) /\ (g X Y Z))
 * --> d == \\\ Exists\\ #4=#5 /\ (#3=(f #5 #1) /\ (g #5 #1 #2))
 *)
let mk_clause pred params body =
  (* pred       d
   * params     [X;X;(f X Y)]
   * Create the prolog (new equalities added to the body) and the new set
   * of variables used as parameters.
   * A parameter can be left untouched if it's a variable which didn't
   * occur yet. *)
  let new_params,prolog =
    List.fold_left
      (fun (new_params,prolog) p ->
         match Term.observe p with
           | Term.Var {Term.tag=Term.Logic}
               when List.for_all (fun v -> v!=p) new_params ->
               p::new_params,prolog
           | _  ->
               let v = Term.fresh ~ts:0 ~lts:0 Term.Logic in
               (v::new_params,(Term.op_eq v p)::prolog))
      ([],[])
      params
  in
  (* new_params [V;U;X]
   * prolog     [V=(f X Y);U=X]
   * Add prolog to the body *)
  let body = if prolog = [] then body else
    List.fold_left
      (fun acc term -> Term.op_and term acc)
      body
      prolog
  in
  (* body       U=X /\ (V=(f X Y) /\ (g X Y Z))
   * Quantify existentially over the initial free variables. *)
  let body =
    List.fold_left
      (fun body v ->
         if List.exists (Term.eq v) new_params then body
         else Term.quantify Term.Exists v body)
      body
      (* XXX in case [body] wasn't created by [translate_term],
       * we should depend on the level to look for instantiable variables,
       * ie not always Logic ones (cf [translate_term]) *)
      (Term.logic_vars [body])
  in
  if !debug then
    Format.eprintf "%a := %a@."
      Pprint.pp_term (Term.app pred (List.rev new_params))
      Pprint.pp_term body ;
  (* body       Exists\\ U=X /\ (V=(f X #1) /\ (g X #1 #2))
   * Finally, abstract over parameters *)
  let arity,body =
    if new_params = [] then 0,body else
      let body =
        List.fold_left (fun body v -> Term.abstract v body)
          body
          new_params
      in match Term.observe body with
        | Term.Lam (n,b) -> n,b
        | _ -> assert false
  in
  (* pred       d
   * arity      3
   * body       Exists\\ #4=#5 /\ (#3=(f #5 #1) /\ (g #5 #1 #2)) *)
  (pred, arity, body)

let get_pred head_var fail_const fail_missing =
  try begin
    match Hashtbl.find defs head_var with
      | Constant _ -> fail_const ()
      | Predicate x -> x
  end with Not_found -> fail_missing ()

let mk_def_clause p head body =
  let pred,params = match Term.observe head with
    | Term.Var ({Term.tag=Term.Constant}) -> head,[]
    | Term.App (pred,params) -> pred,params
    | _ -> raise (Inconsistent_definition
                    ("some predicate",p,"head term structure incorrect"))
  in
  mk_clause pred params body

let add_def_clause new_predicates (p,pre_head,pre_body) =
  let free_types : (Term.var,Typing.ty) Hashtbl.t =
    Hashtbl.create 10
  in
  let phead_name = Input.pred_name pre_head in 
  let free_args = Input.free_args pre_head in
  let head,_ = translate_term ~phead_name ~free_args pre_head free_types in
  let body,_ = translate_term ~phead_name ~free_args pre_body free_types in
  let pred,arity,body =
    mk_def_clause p head body
  in
  let head_var = Term.get_var pred in
  let name = Term.get_name pred in
  let f,b,th,t,ty =
    get_pred head_var
      (fun () -> raise (Inconsistent_definition
                          (name,p,"object declared as a constant")))
      (fun () -> raise (Inconsistent_definition
                          (name,p,"predicate not declared")))
  in
  if List.exists (fun (v,_) -> v == head_var) new_predicates then begin
    let b =
      match b with
        | None -> Term.lambda arity body
        | Some b ->
            begin match Term.observe b with
              | Term.Lam (a,b) when arity=a ->
                  Term.lambda a (Term.op_or b body)
              | _ when arity=0 ->
                  Term.op_or b body
              | _ -> assert false
            end
    in
    let b = Norm.hnorm b in
    Hashtbl.replace defs head_var (Predicate (f,Some b,th,t,ty)) ;
  end else raise (Inconsistent_definition
                    (name,p,"predicate not declared in this block"))

let add_clauses new_predicates clauses =
  List.iter (add_def_clause new_predicates) clauses


(* theorem definitions *)

exception Inconsistent_theorem of string * Input.pos * string


let mk_theorem_clauses (p,n) theorem =
  (* Check whether the theorem has the right structure. *)
  let clean_theorem theorem =
    let vars =
      let rec aux l = function
        | n when n <= 0 -> l
        (* XXX in case [translate_term] changes how it deals with free variables,
         * we should depend on the level to create an instantiable variable,
         * ie not always a Logic one (cf [mk_clause] and [translate_term])*)
        | n -> aux ((Term.fresh ~ts:0 ~lts:0 Term.Logic)::l) (n-1)
      in
      aux []
    in
    let split head = match Term.observe head with
      | Term.Var ({Term.tag=Term.Constant}) -> head,[]
      | Term.App (pred,params) -> pred,params
      | _ -> raise (Inconsistent_theorem (n,p,"head term structure incorrect"))
    in
    (* [newl] is a list of deep-normed theorem clauses
     * [oldl] is a list of theorems built with theorem clauses, /\ and -> *)
    let rec aux newl = function
      | [] -> newl
      | theorem::oldl ->
          let theorem = Norm.hnorm theorem in
          begin match Term.observe theorem with
            | Term.Binop (Term.Arrow,body,head) ->
                let head = Norm.deep_norm head in
                let body = Norm.deep_norm body in
                let pred,params = split head in
                aux ((pred,params,body)::newl) oldl
            | Term.Binder (Term.Forall,n,t) ->
                let t = Term.lambda n t in
                aux newl ((Term.app t (vars n))::oldl)
            | Term.Binop (Term.And,t1,t2) ->
                aux newl (t1::t2::oldl)
            (* TODO allow atomic facts,
             * ie auto-translate "p X" to "true -> p X" *)
            | _ ->
                let head = Norm.deep_norm theorem in
                let pred,params = split head in
                aux ((pred,params,Term.op_true)::newl) oldl
          end
    in
    aux [] [theorem]
  in
  List.rev_map
    (fun (pred,params,body) -> mk_clause pred params body)
    (clean_theorem theorem)

let add_theorem_clause p (pred,arity,body) =
  let head_var = Term.get_var pred in
  let name = Term.get_name pred in
  let f,b,th,t,ty =
    get_pred head_var
      (fun () -> raise (Inconsistent_theorem
                          (name,p,"target object declared as a constant")))
      (fun () -> raise (Inconsistent_theorem
                          (name,p,"predicate not declared")))
  in
  let th =
    match th with
      | None -> Term.lambda arity body
      | Some th ->
          begin match Term.observe th with
            | Term.Lam (a,th) when arity=a ->
                Term.lambda a (Term.op_or th body)
            | _ when arity=0 ->
                Term.op_or th body
            | _ -> assert false
          end
  in
  let th = Norm.hnorm th in
  Hashtbl.replace defs head_var (Predicate (f,b,Some th,t,ty))

let add_theorem (p,n,pre_theorem) =
  let free_types : (Term.var,Typing.ty) Hashtbl.t =
    Hashtbl.create 10
  in
  let theorem,_ = translate_term pre_theorem free_types in
  let clauses = mk_theorem_clauses (p,n) theorem in
  List.iter (add_theorem_clause p) clauses


(* Using predicates *)

exception Missing_definition of string * Typing.pos option
exception Missing_table of string * Typing.pos option


let reset_decls () =
  Hashtbl.clear defs ;
  Hashtbl.clear type_kinds

let get_name_pred ?pos head_tm failure =
  let head_var = Term.get_var head_tm in
  let name = Term.get_name head_tm in
  let x =
    get_pred head_var
      (fun () -> failure () ; raise (Missing_definition (name,pos)))
      (fun () -> failure () ; raise (Missing_declaration (name,pos)))
  in
  name,x

let get_def ~check_arity head_tm =
  let _,(f,b,th,t,ty) = get_name_pred head_tm ignore in
  (* XXX in the case of an empty definition (b = None),
   * we can't infer the arity of the predicate,
   * so the actual value of the body returned should be
   * Lam (n,False) with an a priori unknown n, which isn't possible.
   * Therefore, so long as we allow empty definitions and hollow types,
   * [check_arity] is mandatory. *)
  let b = match b with
    | None -> Term.lambda check_arity Term.op_false
    | Some b -> b
  in
  let th = match th with
    | None -> Term.lambda check_arity Term.op_false
    | Some th -> th
  in
  f,b,th,t,ty

let update_def head_tm body = 
  let _,(f,b,th,t,ty) = get_name_pred head_tm ignore in
  let head_var = Term.get_var head_tm in
  Hashtbl.replace defs head_var (Predicate (f,Some body,th,t,ty))

let remove_def head_tm =
  let head_var = Term.get_var head_tm in
  Hashtbl.remove defs head_var

let get_table pos head_tm success failure =
  let name,(_,_,_,table,ty) = get_name_pred ~pos head_tm failure in
  match table with
    | Some table -> success table ty
    | None -> failure () ; raise (Missing_table (name,Some pos))

let clear_tables () =
  Hashtbl.iter
    (fun _ v -> match v with
       | Predicate (_,_,_,Some t,_) -> Table.reset t
       | _ -> ())
    defs

let clear_table (p,head_tm) =
  get_table p head_tm (fun table _ -> Table.reset table) ignore


(* I/O *)

let print_env () =
  let print_types () =
    Format.printf "@[<v 3>*** Types ***" ;
    Hashtbl.iter
      (fun v k -> Format.printf "@,@[%s :@;<1 2>%a@]"
                    (Term.get_var_name v)
                    Typing.pp_kind k)
      type_kinds ;
    Format.printf "@]@."
  in
  let lc,lp = Hashtbl.fold
                (fun k v (lc,lp) ->
                   match v with
                     | Constant ty ->
                         (Term.get_var_name k,ty)::lc,lp
                     | Predicate (f,_,_,_,ty) ->
                         lc,(Term.get_var_name k,f,ty)::lp)
                defs ([],[])
  in
  let print_constants () =
    Format.printf "@[<v 3>*** Constants ***" ;
    List.iter
      (fun (n,ty) -> Format.printf "@,@[%s :@;<1 2>%a@]"
                     n
                     (fun ty -> Typing.pp_type_norm ty) ty)
      (List.sort (fun (x,_) (y,_) -> compare x y) lc) ;
    Format.printf "@]@."
  in
  let print_predicates () =
    let string_of_flavour = function
      | Normal -> "  "
      | Inductive -> "I "
      | CoInductive -> "C "
    in
    Format.printf "@[<v 1>*** Predicates ***" ;
    List.iter
      (fun (n,f,ty) -> Format.printf "@,@[%s%s :@;<1 4>%a@]"
                       (string_of_flavour f)
                       n
                       (fun ty -> Typing.pp_type_norm ty) ty)
      (List.sort (fun (x,_,_) (y,_,_) -> compare x y) lp) ;
    Format.printf "@]@."
  in
  print_types () ;
  print_constants ();
  print_predicates ()

let get_types pre_term =
  let free_types : (Term.var,Typing.ty) Hashtbl.t =
    Hashtbl.create 10
  in
  let ty = Typing.fresh_typaram () in
  let t,ty = translate_term ~infer:false ~expected_type:ty pre_term free_types in
  t,ty,free_types

let print_type_of pre_term =
  let t,ty,free_types = get_types pre_term in
  Format.printf "@[<v 3>@[%a :@;<1 2>%a@]"
    Pprint.pp_term t
    Typing.pp_type ty ;
  Hashtbl.iter
    (fun v ty -> Format.printf "@,@[%s :@;<1 2>%a@]"
                   (Term.get_var_name v)
                   (fun ty -> Typing.pp_type_norm ty) ty)
    free_types ;
  Format.printf "@]@."

let show_table (p,head_tm) =
  get_table p head_tm (fun table _ -> Table.print head_tm table) ignore

let save_table (p,head_tm) file =
  try
    let fout = open_out_gen [Open_wronly;Open_creat;Open_excl] 0o600 file in
    try
      get_table p head_tm
        (fun table ty -> Table.fprint fout head_tm table ty ; close_out fout)
        (fun () -> close_out fout)
    with Sys_error e ->
      Format.printf "Couldn't close file (%s).@." e
  with Sys_error e ->
    Format.printf "Couldn't open file for writing (%s).@." e


(* Misc *)

(* Handle user interruptions *)
let interrupt = ref false
exception Interrupt
let _ =
  Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ -> interrupt := true))
let check_interrupt () =
  if !interrupt then ( interrupt := false ; true ) else false
