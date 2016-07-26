(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006-2012 David Baelde, Alwen Tiu                          *)
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

(* Option to turn on/off equivariant indexing. *)
let eqvt_index = ref true

(* In the tree, variables are identified by uniques numbers, which I'll call
 * the [VID] (variable id). We could get rid of that and rely only on the order
 * in which we meet the vars in the tree, but that would involve extra
 * care when changing an algorithm (insertion/lookup or fold).
 * So at the end of a branch we have a collection of variables with [VID]s,
 * and we want to store a constraint describing this collection, such that
 * two formulas satisfying the same rigid structure and map are indeed
 * logically equivalent.
 * We first get rid of [VID]s, which are not necessarily \[0,1,2..n\],
 * and renumber variables using [CID]s (constraint id) from 0 to n.
 * In the leaf we store:
 * - the maximum [VID]
 * - an array mapping [CID] to [VID]
 * In the constraint we store:
 * - an array describing variable equalities: to each variable (denoted by its
 *   [CID]) is associated the smallest (in term of [CID]) equal variable.
 * - the array mapping [CID]s to local timestamps. *)
type constraints = { eq      : int array ;
                     lts     : int array }

let dummy_var = Term.get_var (Term.fresh ~ts:(-1) ~lts:(-1) Term.Constant)

exception Found of int

let get_leaf bindings =
  let n = List.length bindings in
  (* Sorting might be a useless precautions since we always parse the index
   * in the same order, but it's not critical and I need the max anyway. *)
  let bindings = List.sort (fun (i,_) (j,_) -> compare j i) bindings in
  let max_vid = match bindings with (m,_)::_ -> m | _ -> 0 in
  let vid = Array.make n 0 in
  (* We prepare the constraints array,
   * and transform the [(int*var) list] into a more convenient [var array]. *)
  let c = {
    eq      = Array.make n 0 ;
    lts     = Array.make n 0 }
  in
  let v = Array.make n dummy_var in
  let _ =
    List.fold_left
      (fun j (i,x) ->
         vid.(j) <- i ;
         c.lts.(j) <- x.Term.lts ;
         v.(j) <- x ;
         (* [c.eq.(j)] gets the least index which has an equal value *)
         c.eq.(j) <-
         begin try
           for k = 0 to j do
             if v.(k) = x then raise (Found k)
           done ;
           assert false
         with Found k -> k
         end ;
         j+1)
      0 bindings
  in
  max_vid,vid,c

let get_constraints bindings =
  let _,_,constraints = get_leaf bindings in constraints

let get_vars max_vid vid c =
  let table = Array.make (max_vid+1) (Term.db 0) in
  let l = ref [] in
  for i = 0 to Array.length c.eq - 1 do
    table.(vid.(i)) <-
    if c.eq.(i) = i then begin
      let t = Term.fresh Term.Eigen ~ts:0 ~lts:0 in
      l := t :: !l ;
      t
    end else
      table.(vid.(c.eq.(i)))
  done ;
  table,(List.rev !l)

module ConstraintsOrdered = struct
  type t = constraints
  let compare = compare
end
module ConstraintsMap = Map.Make(ConstraintsOrdered)

let new_leaf bindings data =
  let map = ConstraintsMap.empty in
  let max_vid,vid,constraints = get_leaf bindings in
  max_vid,vid,ConstraintsMap.add constraints data map

let update_leaf (max_vid,vid,map) bindings data =
  let constraints = get_constraints bindings in
  let map = match data with
    | Some data -> ConstraintsMap.add constraints data map
    | None -> ConstraintsMap.remove constraints map
  in
  max_vid,vid,map

let find_leaf (_,_,map) bindings =
  let constraints = get_constraints bindings in
  try Some (ConstraintsMap.find constraints map)
  with Not_found -> None


(* == Indexing ============================================================= *)

(*  Patterns allow universal (constant-like) variables,
 *  existential (instantiable) variables,
 *  and nabla variables as deBruijn indices. *)
type pattern =
  | QString of string
  | Nat    of int
  | DB     of int
  | NB     of int
  | UVar   of int
  | Cst    of Term.term * Term.var
  | EVar   of int
  | True
  | False
  | Binop  of Term.binop * pattern * pattern
  | Binder of Term.binder * int * pattern
  | Lam    of int * pattern
  | App    of int * pattern list (* Store the length of the list *)
  | Hole

type 'a index   = 'a children * 'a node list (* when on a Leaf, nodes=[] *)
and 'a children = Leaf of 'a leaf | Refine
and 'a leaf     = int * int array * 'a ConstraintsMap.t
and 'a node     = Node of (pattern list * 'a index)

type 'a zipper =
  | Top
  | Zip of 'a children                           (* flag of our father *)
    * 'a node list * pattern list * 'a node list (* siblings and arc *)
    * 'a zipper                                  (* location of our father *)
type 'a t = 'a index * 'a zipper

let empty = (Refine,[]),Top

let rec z_top = function
  | index,Top -> index,Top
  | index,Zip (children,older,patterns,younger,zipper) ->
      let index =
        children,(List.rev_append older ((Node (patterns,index))::younger))
      in
      z_top (index,zipper)


exception Cannot_table

(* [create_node bindings terms data] compiles the terms into patterns
 * and associates them with a leaf containing the data.
 * [terms] is expected to be reversed. *)
let create_node
      ~allow_universal ~allow_existential ~switch_vars
      bindings terms data =
  let bindings = List.sort (fun (i,_) (j,_) -> compare i j) bindings in
  let add bindings v =
    let rec aux accu expect = function
      | (i,x)::l when i=expect -> aux ((i,x)::accu) (expect+1) l
      | l -> expect, List.rev_append accu ((expect,v)::l)
    in
    aux [] 0 bindings
  in
  let rec compile bindings term =
    let term = Norm.hnorm term in
    match Term.observe term with
      | Term.QString s -> QString s,bindings
      | Term.Nat s -> Nat s,bindings
      | Term.DB i -> DB i, bindings
      | Term.NB i -> NB i, bindings
      | Term.Var ({Term.tag=Term.Eigen} as var)
          when (not switch_vars) & allow_universal ->
          let i,bindings = add bindings var in
          UVar i, bindings
      | Term.Var ({Term.tag=Term.Logic})
          when switch_vars & allow_universal ->
          failwith "logic variable forbidden here"
          (*let i,bindings = add bindings var in
          UVar i, bindings*)
      | Term.Var ({Term.tag=Term.Constant} as v) ->
          Cst (Term.deref term,v), bindings
      | Term.Var ({Term.tag=Term.Logic} as var)
          when (not switch_vars) & allow_existential ->
          let i,bindings = add bindings var in
          EVar i, bindings
      | Term.Var ({Term.tag=Term.Eigen} as var)
          when switch_vars & allow_existential ->
          let i,bindings = add bindings var in
          EVar i, bindings
      | Term.True -> True, bindings
      | Term.False -> False, bindings
      | Term.Binop (b,t1,t2) ->
          let pat1,bindings = compile bindings t1 in
          let pat2,bindings = compile bindings t2 in
          Binop (b,pat1,pat2),bindings
      | Term.Binder (b,n,t) ->
          let pat,bindings = compile bindings t in
          Binder (b,n,pat),bindings
      | Term.Lam (i,t) ->
          let pat,bindings = compile bindings t in
          Lam (i,pat),bindings
      | Term.App (h,terms) ->
          let terms = h::terms in
          let patterns,bindings =
            List.fold_left
              (fun (pats,b) t ->
                 let (p,b) = compile b t in
                 (p::pats,b))
              ([],bindings)
              terms
          in
          App (List.length terms, List.rev patterns),bindings
      | _ -> raise Cannot_table
  in
  let patterns,bindings =
    List.fold_left
      (fun (pats,binds) term ->
         let pat,binds = compile binds term in
           pat::pats,binds)
      ([],bindings)
      terms
  in
  patterns,Leaf (new_leaf bindings data)

(* [superficial_match] expects a head-normalized term. *)
let superficial_match ~switch_vars patterns terms =
  let sub (pat,term) =
    match pat, Term.observe term with
      | QString s1,Term.QString s2 -> s1=s2
      | Nat i,Term.Nat j
      | DB i, Term.DB j
      | NB i, Term.NB j -> i=j
      | UVar _, Term.Var {Term.tag=Term.Eigen} -> not switch_vars
      | UVar _, Term.Var {Term.tag=Term.Logic} -> switch_vars
      | Cst (_,v), Term.Var v' -> v==v'
      | EVar _, Term.Var {Term.tag=Term.Logic} -> not switch_vars
      | EVar _, Term.Var {Term.tag=Term.Eigen} -> switch_vars
      | True, Term.True
      | False, Term.False -> true
      | Binop (b1,_,_), Term.Binop (b2,_,_) -> b1=b2
      | Binder (b1,n1,_), Term.Binder (b2,n2,_) -> b1=b2 && n1=n2
      | Lam (i,_), Term.Lam (j,_) -> i=j
      | App (i,_), Term.App (h,l) -> i = 1 + List.length l
      | Hole, _ -> true
      | _ -> false
  in
  List.for_all sub (List.map2 (fun a b -> a,b) patterns terms)

(* [superficial_sort] sorts patterns directly contained in a list
 * according to their top-level symbol.
 * It uses hardcoded rankings for terms, binary operators
 * (the same that in Pprint, but hardcoded once more) and quantifiers.
 * TODO un-hardcode and share some code with Pprint.
 * A solution would be to take the binop and binder rankings as arguments
 * (defined in Pprint, where they belong), and to replace the ranking on terms,
 * which is actually a ranking on patterns and therefore cannot leave Index,
 * by an actual ranking on terms defined in Term
 * and used during the [update] stage. *)
let superficial_sort nodes =
  let rank = function
    | QString _ -> 0
    | Nat _ -> 1
    | DB _ -> 2
    | NB _ -> 3
    | UVar _ -> 4
    | Cst _ -> 5
    | EVar _ -> 6
    | True -> 7
    | False -> 8
    | Binop _ -> 9
    | Binder _ -> 10
    | Lam _ -> 11
    | App _ -> 12
    | Hole -> 13
  in
  let comp pat1 pat2 = match pat1,pat2 with
    | QString s1,QString s2 -> compare s1 s2
    | Nat i1,Nat i2 | DB i1,DB i2 | NB i1,NB i2
    | UVar i1,UVar i2 | EVar i1,EVar i2 -> compare i1 i2
    | Cst (t1,_),Cst (t2,_) -> compare (Term.get_name t1) (Term.get_name t2)
    | Binop (b1,_,_),Binop (b2,_,_) ->
        begin let priorities = function
          | Term.Eq -> 4
          | Term.And -> 3
          | Term.Or -> 2
          | Term.Arrow -> 1
        in
        compare (priorities b1) (priorities b2) end
    | Binder (b1,_,_),Binder (b2,_,_) ->
        begin let priorities = function
          | Term.Forall -> 3
          | Term.Exists -> 2
          | Term.Nabla -> 1
        in
        compare (priorities b1) (priorities b2) end
    | Lam (i1,_),Lam (i2,_)
    | App (i1,_),App (i2,_) -> compare i1 i2
    | _,_ -> compare (rank pat1) (rank pat2)
  in
  let multicomp (Node (l1,_)) (Node (l2,_)) =
    let rec aux = function
        | [],[] -> 0
        | [],_ | _,[] -> assert false
        | h1::l1,h2::l2 ->
            begin match comp h1 h2 with
              | 0 ->  aux (l1,l2)
              | n -> n
            end
    in
    aux (l1,l2)
  in
  List.sort multicomp nodes

(* [rename] Renaming nabla variables in a term according to the order of
 *   traversal in the tree representation of the (normal form of the) term.
 *   This is a cheap way to force equivariant matching in tables.
 * Added by Tiu, 03 March 2011. *)

let rec rename term bindings n =
  let term = Norm.hnorm term in
  match Term.observe term with
    | Term.QString _ | Term.Nat _ | Term.DB _
    | Term.Var _ | Term.True | Term.False ->
        term, bindings, n
    | Term.NB i ->
        begin try
          let j = List.assoc i bindings in
          Term.nabla j, bindings, n
        with Not_found -> Term.nabla (n+1), (i,n+1)::bindings, n+1
        end
    | Term.Binop (b,t1,t2) ->
        let t1,bindings,n = rename t1 bindings n in
        let t2,bindings,n = rename t2 bindings n in
        Term.op_binop b t1 t2,bindings,n
    | Term.Binder (b,i,t) ->
        let t,bindings,n = rename t bindings n in
        Term.binder b i t,bindings,n
    | Term.Lam (i,t) ->
        let t,bindings,n = rename t bindings n in
        (Term.lambda i t),bindings,n
    | Term.App (h,terms) ->
        let newh,bds,n'= rename h bindings n in
        let newterms,bds,n'=
          List.fold_left
            (fun (ts,bd,idx) t ->
               let t',bd',idx' = rename t bd idx
               in (t'::ts,bd',idx'))
            ([],bds,n')
            terms
        in
        (Term.app newh (List.rev newterms)),bds,n'
    | _ -> raise Cannot_table

let nb_rename terms =
  let newterms,_,_ =
    List.fold_left
      (fun (ts,bd,idx) t ->
         let t',bd',idx' = rename t bd idx
         in (t'::ts,bd',idx'))
      ([],[],0)
      terms
  in List.rev newterms


(* == ACCESS =============================================================== *)

(* TODO Some of these are tailrec, some waste this effort..
 *      Everything can be done tailrec using a zipper. *)

(* Expects hnorm-ed terms. *)
let access
      ~allow_universal ~allow_existential ~switch_vars
      zindex terms =
  (* [access_pattern] filters a term through a pattern,
   * XXX whatup on mismatch? XXX
   * returns the list of bindings,
   * returns the reversed list of catches and
   * returns the reversed list of former patterns.
   * XXX beware of allow_universal and switch_vars! XXX
   * Returns hnorm-ed terms. *)
  let rec access_pattern bindings catches former_pats pattern term =
    let term = Norm.hnorm term in
    match pattern, Term.observe term with
      | QString s1, Term.QString s2 when s1=s2 ->
          (false, pattern, bindings, catches, former_pats)
      | Nat i, Term.Nat j
      | DB i, Term.DB j
      | NB i, Term.NB j when i = j ->
          (false, pattern, bindings, catches, former_pats)
      | UVar v, Term.Var ({Term.tag=Term.Eigen} as var)
          when (not switch_vars) & allow_universal ->
          (false, pattern, (v,var)::bindings, catches, former_pats)
      | UVar v, Term.Var ({Term.tag=Term.Logic})
          when switch_vars & allow_universal ->
          failwith "logic variable forbidden here"
          (*(false, pattern, (v,var)::bindings, catches, former_pats)*)
            (*
      | UVar v, Term.Var ({Term.tag=Term.Constant} as var) ->
          Format.eprintf "comparaison UVar/Constant@." ;
          (false, pattern, (v,var)::bindings, catches, former_pats)
             *)
      | Cst (_,c), Term.Var c' when c==c' ->
          (false, pattern, bindings, catches, former_pats)
            (*
      | Cst (_,_), Term.Var ({Term.tag=Term.Logic})
          when (not switch_vars) ->
          Format.eprintf "comparaison Const/Logic@." ;
          (false, pattern, bindings, catches, former_pats)
             *)
            (*
      | Cst (_,_), Term.Var ({Term.tag=Term.Eigen})
          when switch_vars ->
          Format.eprintf "comparaison Const/Eigen@." ;
          (false, pattern, bindings, catches, former_pats)
             *)
      | EVar v, Term.Var ({Term.tag=Term.Logic} as var)
          when (not switch_vars) & allow_existential ->
          (false, pattern, (v,var)::bindings, catches, former_pats)
      | EVar v, Term.Var ({Term.tag=Term.Eigen} as var)
          when switch_vars & allow_existential ->
          (false, pattern, (v,var)::bindings, catches, former_pats)
      | True, Term.True | False, Term.False ->
          (false, pattern, bindings, catches, former_pats)
      | Binop (b1,pat1,pat2), Term.Binop (b2,t1,t2) when b1=b2 ->
          let (changed1,pat1,bindings,catches,former_pats) =
            access_pattern bindings catches former_pats pat1 t1
          in
          let (changed2,pat2,bindings,catches,former_pats) =
            access_pattern bindings catches former_pats pat2 t2
          in
          (changed1 || changed2, Binop (b1,pat1,pat2), bindings, catches, former_pats)
      | Binder (b1,n1,pat), Term.Binder (b2,n2,t) when b1=b2 && n1=n2 ->
          let (changed,pat,bindings,catches,former_pats) =
            access_pattern bindings catches former_pats pat t
          in
          (changed, Binder (b1,n1,pat), bindings, catches, former_pats)
      | Lam (i,pattern), Term.Lam (j,term) when i = j ->
          let (changed,pattern,bindings,catches,former_pats) =
            access_pattern bindings catches former_pats pattern term
          in
          (changed, Lam (i,pattern), bindings, catches, former_pats)
      | App (i,patterns), Term.App (h,l) when i = 1 + List.length l ->
          let (changed,patterns,bindings,catches,former_pats) =
            access_patterns bindings catches former_pats patterns (h::l)
          in
          let patterns = List.rev patterns in
          assert (List.length patterns = i) ;
          (changed, App (i,patterns), bindings, catches, former_pats)
      | Hole,_ ->
          (false, Hole, bindings, term::catches, Hole::former_pats)
      | _ ->
          (true, Hole, bindings, term::catches, pattern::former_pats)
  and access_patterns bindings catches former_pats patterns terms =
    List.fold_left2
      (fun (changed,patterns,bindings,catches,former_pats) pattern term ->
         (* Go through one pattern, enrich catches and bindings,
          * and build the updated pattern. *)
         let (changed',pattern,bindings,catches,former_pats) =
           access_pattern bindings catches former_pats pattern term
         in
         changed'||changed,pattern::patterns,bindings,catches,former_pats)
      (false,[],bindings,catches,former_pats)
      patterns
      terms
  in
  (* Expects hnorm-ed terms. *)
  let rec access_node bindings terms zipper older_nodes nodes patterns index =
    let changed,patterns,bindings,catches,former_pats =
      access_patterns bindings [] [] patterns terms
    in
    let patterns = List.rev patterns in
    let zipper = Zip (Refine,older_nodes,patterns,nodes,zipper) in
    if changed then
      (* The new patterns have some new holes, we separate the new and the
       * former terms by adding an intermediate index.
       * We need to compile the caught terms into patterns. *)
      (fun data ->
         let patterns,children =
           create_node ~allow_universal ~allow_existential ~switch_vars
             bindings catches data
         in
         let newnode = Node (patterns,(children,[])) in
         let oldnode = Node (List.rev former_pats,index) in
         let index = Refine,[newnode ; oldnode] in
         z_top (index,zipper)),
      None
    else
        (* The terms were fully matched by the patterns,
         * the new [patterns] is the same as the former one,
         * the access gets propagated deeper without changing anything here. *)
        access_index bindings (List.rev catches) (index,zipper)
  and access_nodes bindings terms zipper older_nodes = function
    | [] ->
        (fun data ->
           let patterns,children =
             create_node ~allow_universal ~allow_existential ~switch_vars
               bindings (List.rev terms) data
           in
           let index = children,[] in
           let zipper = Zip (Refine,older_nodes,patterns,[],zipper) in
           z_top (index,zipper)),
        None
    | (Node (patterns,index) as node)::nodes ->
        if superficial_match ~switch_vars patterns terms then
          access_node bindings terms zipper older_nodes nodes patterns index
        else
          access_nodes bindings terms zipper (node::older_nodes) nodes
  (* access an index, i.e. an (unordered) list of alternative nodes.
   * Expects hnorm-ed terms. *)
  and access_index bindings terms (index,zipper) = match terms,index with
    | [],(Leaf leaf,[]) ->
        (fun data ->
           let index = Leaf (update_leaf leaf bindings (Some data)),[] in
           z_top (index,zipper)),
        find_leaf leaf bindings
    | _,(Refine,nodes) ->
        access_nodes bindings terms zipper [] nodes
    | _ -> assert false
  in
  access_index [] terms zindex

let access
      ~allow_universal ~allow_existential ~switch_vars
      zindex terms =
  assert (not allow_existential) ;
  assert (not (allow_universal=switch_vars)) ;
  let terms =
    if !eqvt_index then (nb_rename terms) else (List.map Norm.hnorm terms)
  in
  let update,found =
    access ~allow_universal ~allow_existential ~switch_vars zindex terms
  in
  (* TODO implement a real [delete] *)
  let delete () = zindex in
  update,found,delete


(* == FOLD ================================================================== *)

(* We use some kind of multi-locations zippers
 * XXX merge with the main zipper? *)

module type MZ_t =
sig
  type t
  val empty : t
  val refine : t -> pattern list -> t
  val zip : Term.term array -> t -> Term.term list
end

module MZ : MZ_t =
struct

  type item =
    | ZQString of string
    | ZNat    of int
    | ZDB     of int
    | ZNB     of int
    | ZVar    of int
    | ZCst    of Term.term * Term.var
    | ZTrue
    | ZFalse
    | ZBinop  of Term.binop
    | ZBinder of Term.binder * int
    | ZLam    of int
    | ZApp    of int
    | ZHole

  type t = item list list

  let arity = function
    | ZBinop _ -> 2
    | ZBinder _ | ZLam _ | ZHole -> 1
    | ZApp n -> n
    | _ -> 0

  let arity = function
    | [] -> assert false
    | row::_ -> List.fold_left (+) 0 (List.map arity row)

  let empty = []

  let compile_step pats =
    let row,subpats =
      List.fold_left
        (fun (row,subpats) -> function
           | QString s -> (ZQString s)::row,subpats
           | Nat i -> (ZNat i)::row,subpats
           | DB i  ->  (ZDB i)::row, subpats
           | NB i  ->  (ZNB i)::row, subpats
           | UVar i | EVar i -> (ZVar i)::row, subpats
           | Cst (t,c) -> (ZCst (t,c))::row, subpats
           | True -> ZTrue::row, subpats
           | False -> ZFalse::row, subpats
           | Binop (b,p1,p2) -> (ZBinop b)::row, p2::p1::subpats
           | Binder (b,n,p) -> (ZBinder (b,n))::row, p::subpats
           | App (n,l) -> (ZApp n)::row, List.rev_append l subpats
           | Lam (n,p) -> (ZLam n)::row, p::subpats
           | Hole -> ZHole::row, Hole::subpats)
        ([],[])
        pats
    in
    List.rev row,List.rev subpats

  let rec refine acc patterns =
    if List.for_all ((=) Hole) patterns then acc else
      let row,sub = compile_step patterns in
      refine (row::acc) sub

  let split_at_nth l n =
    let rec aux before l n = match l,n with
      | _,0 -> List.rev before,l
      | h::l,_ -> aux (h::before) l (n-1)
      | _ -> assert false
    in
    aux [] l n

  let zip table mz =
    let zip_step terms = function
      | ZQString s -> Term.qstring s,terms
      | ZNat i -> Term.nat i,terms
      | ZDB i  -> Term.db i, terms
      | ZNB i  -> Term.nabla i, terms
      | ZVar i -> table.(i), terms
      | ZCst (t,_) -> t, terms
      | ZTrue -> Term.op_true, terms
      | ZFalse -> Term.op_false, terms
      | ZBinop b ->
          begin match terms with
            | t1::t2::terms ->
                Term.op_binop b t1 t2, terms
            | _ -> assert false
          end
      | ZBinder (b,n) ->
          begin match terms with
            | h::terms ->
                Term.binder b n h, terms
            | _ -> assert false
          end
      | ZLam n ->
          begin match terms with
            | h::terms -> Term.lambda n h, terms
            | _ -> assert false
          end
      | ZApp n ->
          begin match split_at_nth terms n with
            | (h::tl),terms ->
                Term.app h tl, terms
            | _ -> assert false
          end
      | ZHole ->
          begin match terms with
            | h::terms -> h, terms
            | _ -> assert false
          end
    in
    let rec zip terms row =
      let out,terms =
        List.fold_left
          (fun (out,terms) item ->
             let t,terms = zip_step terms item in
             t::out,terms)
          ([],terms)
          row
      in
      assert (terms = []) ;
      List.rev out
    in
    List.fold_left zip [] mz

end

let iter (index,_) f =
  let rec iter_node mz (Node (patterns,index)) =
    iter_index (MZ.refine mz patterns) index
  and iter_index mz = function
    | Leaf (max_vid,vid,map),[] ->
        ConstraintsMap.iter
          (fun c v ->
             let table,l = (get_vars max_vid vid c) in
             let head = Term.fresh Term.Eigen ~ts:0 ~lts:0 in
             let t = Term.app head (MZ.zip table mz) in
             let t =
               List.fold_left
                 (fun t v -> Term.abstract v t)
                 t
                 l
             in
             f (Term.abstract head t) v)
          map
    | Refine,nodes -> List.iter (iter_node mz) (superficial_sort nodes)
    | _ -> assert false
  in
  iter_index MZ.empty index
