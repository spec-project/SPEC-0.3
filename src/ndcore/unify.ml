(****************************************************************************)
(* An implementation of Higher-Order Pattern Unification                    *)
(* Copyright (C) 2006-2009 Nadathur, Linnell, Baelde, Ziegler               *)
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

type error =
  | OccursCheck
  | TypesMismatch
  | ConstClash of (Term.term * Term.term)

exception Error of error
exception NotLLambda of Term.term
exception Formula_as_Term of Term.term

let fat x = raise (Formula_as_Term x)
let not_ll x = raise (NotLLambda x)
let raise e = raise (Error e)

module type Param =
sig
  val instantiatable : Term.tag
  val constant_like  : Term.tag
end

module Make (P:Param) =
struct

open P
open Term

let (isLeft, isRight) = (P.instantiatable = Eigen, P.instantiatable = Logic)

let constant tag =
  tag = Constant || tag = constant_like
let variable tag =
  tag = instantiatable
let fresh = fresh instantiatable

(* Transforming a term to represent substitutions under abstractions *)
let rec lift t n = match observe t with
  | True | False
  | Binop _ | Binder _ ->
      fat t
  | QString _ | Nat _ | Var _ -> t
  | DB i -> db (i+n)
  | _ -> susp t 0 n []

(* Transforming a list of arguments to represent eta fluffing *)
let rec lift_args l n = match l,n with
  | [],0 -> []
  | [],n -> (db n)::lift_args [] (n-1)
  | (a::rargs),n -> (lift a n)::lift_args rargs n

(* Check wether a Var appears in a list of terms *)
let rec unique_var v = function
  | [] -> true
  | t::rargs  ->
      begin match observe t with
        | True | False
        | Binop _ | Binder _ ->
            fat t
        | Var v' when v=v' -> false
        | _ -> unique_var v rargs
      end

(* Check if a bound variable appears in a list of term *)
let rec unique_bv n l = match l with
  | [] -> true
  | t::rargs ->
      begin match observe t with
        | True | False
        | Binop _ | Binder _ ->
            fat t
        | DB j when n = j -> false
        | _ -> unique_bv n rargs
      end

let rec unique_nb n l = match l with
  | [] -> true
  | t::tl ->
      begin match observe t with
        | True | False
        | Binop _ | Binder _ ->
            fat t
        | NB j when j=n -> false
        | _ -> unique_nb n tl
      end

(* [check_flex_args l fts] checks that a list of terms meets the LLambda
 * requirements for the arguments of a flex term whose timestamp is [fts].
 * @raise NotLLambda if the list doesn't satisfy the requirements. *)
let rec check_flex_args l fts flts =
  match l with
    | [] -> ()
    | t::q ->
        begin match observe t with
          | True | False
          | Binop _ | Binder _ ->
              fat t
          | Var v when constant v.tag && v.ts>fts && unique_var v q ->
              check_flex_args q fts flts
          | DB i when unique_bv i q -> check_flex_args q fts flts
          | NB i when i>flts && unique_nb i q -> check_flex_args q fts flts
          | _ -> not_ll t
        end

(* Simple occurs-check and level check to allow unification in very
 * simple non-llambda cases (when check_flex_args fails).
 * Assumes head-normalization of [t].
 *
 * XXX Note that the level checks are useless on the left (this is in fact
 * true everywhere in this module) and that making them tighter on the right
 * can be dangerous. In a nutshell: this is very simple but suffices. *)
let can_bind v t =
  let rec aux n t =
    match observe t with
      | True | False
      | Binop _ | Binder _ ->
          fat t
      | QString _ | Nat _ -> true
      | Var v' ->
          (isLeft || (v' <> v && v'.ts <= v.ts)) && v'.lts <= v.lts
      | DB i -> i <= n
      | NB j -> j <= v.lts
      | Lam(n', t) -> aux (n+n') t
      | App(h, ts) ->
          aux n h && List.for_all (aux n) (List.map Norm.hnorm ts)
      | Susp _ | Ptr _ -> assert false
  in
  aux 0 t

(* [bvindex bv l n] return a nonzero index iff the db index [bv]
 * appears in [l]; the index is the position from the right, representing
 * the DeBruijn index of the abstraction capturing the argument.
 * Arguments in the list are expected to be head-normalized. *)
let rec bvindex i l n = match l with
  | [] -> 0
  | t::q ->
      begin match observe t with
        | True | False
        | Binop _ | Binder _ ->
            fat t
        | DB j when i=j -> n
        | _ -> bvindex i q (n-1)
      end

let rec nbindex i l n = match l with
  | [] -> 0
  | t::q ->
      begin match observe t with
        | True | False
        | Binop _ | Binder _ ->
            fat t
        | NB j when i=j -> n
        | _ -> nbindex i q (n-1)
      end

(* [cindex c l n] return a nonzero index iff the constant [c]
 * appears in [l]; the index is the position from the right, representing
 * the DeBruijn index of the abstraction capturing the argument.
 * Arguments in the list are expected to be head-normalized. *)
let rec cindex c l n = match l with
  | [] -> 0
  | t::q ->
      begin match observe t with
        | True | False
        | Binop _ | Binder _ ->
            fat t
        | Var c' when c = c' -> n
        | _ -> cindex c q (n-1)
      end

(* Given a flexible term [v1 a11 ... a1n] and another term of the form
 * [... (v2 a21 ... a2m) ...] where [v1] and [v2] are distinct variables,
 * [ts1] and [ts2] being the timestamps associated with [v1] and [v2],
 * and [lev] being the number of abstractions under which [v2] appears
 * embedded in the second term,
 * [raise_and_invert ts1 ts2 [a11 .. a1n] [a21 .. a2m] lev]
 * return a triple consisting of:
 *
 * {ul
 * {li a truth value indicating whether a pruning or raising
 * substitution is needed for [v2],}
 * {li a list of terms [b1 ... bk] such that the term
 * [Lam ... Lam (... (v2' b1 ... bk) ...]
 * represents a unifying substitution for [v1] -- these terms
 * consist of constants from [a11 ... a1n] over which [v2] is
 * possibly raised and inversions of a pruned [a21 ... a2m], and}
 * {li the arguments [c1 ... ck] of a possible "raising" and pruning
 * substitution for [v2] matching the arguments [b1 ... bk] for
 * [v2'] in the second component.}}
 *
 * The composition of the arguments lists can be understood
 * qualitatively as follows:
 *
 * If [ts1 < ts2] then {ul{li the initial part of
 * [b1 ... bk] is the indices of constants from [a11 ... a1n] that do
 * not appear in [a21 ... a2m] and that have a timestamp less than or
 * equal to [ts2] (this corresponds to raising [v2]) and} {li the rest of
 * [b1 ... bk] are the indices (relative to the list a11 ... a1n) of
 * the constants in [a21 ... a2m] that appear in [a11 ... a1n] (these are
 * the arguments that must not be pruned).}} Correspondingly, the first
 * part of the list [c1 ... ck] are the constants from [a11 ... a1n] over
 * which [v2] is "raised" and the second part are the indices relative
 * to [a21 ... a2m] of the constants that are not pruned.
 *
 * If [ts1 >= ts2]
 * then each of [b1 ... bk] is either {ul{li a constant in [a21 ... a2m] that
 * does not appear in [a11 ... a1n] and which has a timestamp less than
 * [ts1] (this corresponds to first raising [v1] and then reducing the
 * substitution generated for [v1])} {li or it is the index, relative to
 * [a11 ... a1n], of the terms in [a21 ... a2m] that are in
 * [a11 ... a1n].}}
 * The list [c1 ... ck] in this case are simply the indices
 * relative to [a21 ... a2m] of the terms in [a21 ... a2m] that are
 * preserved (i.e. not pruned) in [b1 ... bk].
 *
 * This definition assumes that the [aij] are in
 * head-normal form and that [a1] satisfies the LLambda
 * requirements. If [a2] does not satisfy these requirements, an
 * exception will be raised. *)
let raise_and_invert v1 v2 a1 a2 lev =
  let stamps = function {ts=ts;lts=lts} -> ts,lts in
  let ts1,lts1 = stamps v1 in
  let ts2,lts2 = stamps v2 in
  let l1 = List.length a1 in

  (* [raise_var args n] generates the collection of
   * constants in [args] that have a time stamp less than [ts2],
   * assuming [n] is the index for the abstraction corresponding
   * to the first term in [args]. In other words, constants which cannot
   * appear in [v2]'s body.
   * This serves to raise [v2] in the case where [ts1 < ts2]. The boolean
   * component of the returned triple tells if there is
   * any raising to be done. The terms in [args] are assumed to be
   * constants or de Bruijn indices, as head normalized
   * arguments satisfying the LLambda restriction. *)
  let rec raise_var l n = match l with
    | [] -> false,[],[]
    | t::tl ->
        begin match observe t with
          | True | False
          | Binop _ | Binder _ ->
              fat t
          | DB _ -> raise_var tl (n-1)
          | NB j ->
              let raised,inds,consts = raise_var tl (n-1) in
              if j <= lts2 then
                (true,(db (n+lev))::inds,t::consts)
              else
                raised,inds,consts
          | QString _ | Nat _ ->
              let raised,inds,consts = raise_var tl (n-1) in
              (true,(db (n+lev))::inds,t::consts)
          | Var {ts=cts;tag=tag} when constant tag ->
              let raised,inds,consts = raise_var tl (n-1) in
              if cts <= ts2 then
                (true,(db (n+lev))::inds,t::consts)
              else
                (raised,inds,consts)
          | _ -> assert false
        end
  in

  (* [prune args n] "prunes" those items in [args] that are not
   * bound by an embedded abstraction and that do not appear in
   * [a1]. At the same time inverts the items that are not pruned
   * and that are not bound by an embedded abstraction; [n] is assumed to be
   * the length of [args] here and hence yields the index of the
   * leftmost argument position. This pruning computation is
   * relevant to the case when [ts1 < ts2]. The terms in [args]
   * are assumed to be constants or de Bruijn or nabla indices. *)
  let rec prune l n = match l,n with
    | [],0 -> false,[],[]
    | t::q,n ->
        begin match observe t with
          | True | False
          | Binop _ | Binder _ ->
              fat t
          | DB i ->
              let pruned,inds1,inds2 = prune q (n-1) in
                if i > lev then
                  let j = bvindex (i-lev) a1 l1 in
                    if j = 0 then
                      (true,inds1,inds2)
                    else
                      (pruned,
                       (db (j+lev))::inds1,
                       (db n)::inds2)
                else
                  (pruned,t::inds1,(db n)::inds2)
          | QString _ | Nat _ ->
              let pruned,inds1,inds2 = prune q (n-1) in
              (true,inds1,inds2)
          | Var v when constant v.tag ->
              let pruned,inds1,inds2 = prune q (n-1) in
              let j = cindex v a1 l1 in
              if j = 0 then
                (true,inds1,inds2)
              else
                (pruned,
                 (db (j+lev))::inds1,
                 (db n)::inds2)
          | NB i ->
              let pruned,inds1,inds2 = prune q (n-1) in
              let j = nbindex i a1 l1 in
              if j = 0 then
                (true,inds1,inds2)
              else
                (pruned,
                 (db (j+lev))::inds1,
                 (db n)::inds2)
          | _ -> assert false
        end
    | _ -> assert false
  in

  (* Relevant to the case when [ts1 > ts2]. In this case,
   * [prune_and_raise args n] prunes those constants and de
   * Bruijn indices not bound by an embedded abstraction that do
   * not appear in [a1] and, in the case of constants, that have
   * a timestamp greater than [ts1]. These constants are preserved
   * via a raising of [v1].
   * As in prune, [n] is assumed to be the length of the list
   * args. The terms in [args] are assumed to be constants, nabla or
   * de Bruijn indices. *)
  let rec prune_and_raise l n = match l,n with
    | [],0 -> false,[],[]
    | a::q,n ->
        begin match observe a with
          | True | False
          | Binop _ | Binder _ ->
              fat a
          | DB i ->
              let pruned,inds1,inds2 = prune_and_raise q (n-1) in
                if i > lev then
                  let j = bvindex (i-lev) a1 l1 in
                    if j = 0 then
                      (true,inds1,inds2)
                    else
                      (pruned,
                       (db (j+lev))::inds1,
                       (db n)::inds2)
                else
                  (pruned,a::inds1,(db n)::inds2)
          | NB i ->
              let pruned,inds1,inds2 = prune_and_raise q (n-1) in
                if i <= lts1 then
                  pruned,a::inds1,(db n)::inds2
                else
                  let j = nbindex i a1 l1 in
                    if j = 0 then
                      (true,inds1,inds2)
                    else
                      (pruned,
                       (db (j+lev))::inds1,
                       (db n)::inds2)
          | QString _ | Nat _ ->
              let pruned,inds1,inds2 = prune_and_raise q (n-1) in
              (pruned,a::inds1,(db n)::inds2)
          | Var v when constant v.tag ->
              let pruned,inds1,inds2 = prune_and_raise q (n-1) in
              if v.ts <= ts1 then
                (pruned,a::inds1,(db n)::inds2)
              else
                let i = cindex v a1 l1 in
                if i=0 then
                  (true,inds1,inds2)
                else
                  (pruned,
                   (db (i+lev))::inds1,
                   (db n)::inds2)
          | _ -> assert false
        end
    | _ -> assert false
  in

  if ts1<ts2 || lts1<lts2 then
    let raised,args_r1,args_r2 = raise_var a1 l1 in
    let pruned,args_p1,args_p2 = prune a2 (List.length a2) in
    (raised||pruned,args_r1@args_p1,args_r2@args_p2)
  else
    prune_and_raise a2 (List.length a2)

(* Generating the arguments of a pruning substitution for the case
 * when trying to unify two flexible terms of the form (v t_1 ... t_n)
 * and lam ... lam (v s_1 ... s_m) where there are j abstractions at the
 * head of the second term. The first two arguments to prune_same_var
 * are the two lists of arguments, the third argument is j (i.e. the
 * number of abstractions at the head) and the last argument is n+j. It
 * is assumed that type consistency has been checked beforehand,
 * i.e. n+j is indeed equal to m and also that the two argument lists
 * are known to be of the form required for LLambda unification. The
 * computation essentially does the eta fluffing of the first term on
 * the fly (i.e. each t_i has to be lifted over j abstractions and and
 * j new arguments bound by these abstractions are added to the first
 * term). *)
let rec prune_same_var l1 l2 j bl = match l1,l2 with
  | [],[] -> []
  | [],t::q ->
      begin match observe t with
        | True | False
        | Binop _ | Binder _ ->
            fat t
        | DB i when i=j ->
            (db bl)::(prune_same_var [] q (j-1) (bl-1))
        | _ -> prune_same_var [] q (j-1) (bl-1)
      end
  | t1::a1,t2::a2 ->
      begin match observe t1,observe t2 with
        | True,_ | False,_
        | Binop _,_ | Binder _,_ ->
            fat t1
        | _,True | _,False
        | _,Binop _ | _,Binder _ ->
            fat t2
        | QString s1,QString s2 when s1=s2 ->
            (db bl)::(prune_same_var a1 a2 j (bl-1))
        | Var {tag=tag1},Var {tag=tag2}
          when constant tag1 && eq t1 t2 ->
            (db bl)::(prune_same_var a1 a2 j (bl-1))
        | Nat i,Nat j | NB i, NB j when i=j ->
            (db bl)::(prune_same_var a1 a2 j (bl-1))
        | DB i1,DB i2 when i1+j = i2 ->
            (db bl)::(prune_same_var a1 a2 j (bl-1))
        | _ -> prune_same_var a1 a2 j (bl-1)
      end
  | _ -> assert false

(* [makesubst h1 t2 a1] unifies [App (h1,a1) = t2].
 * Given a term of the form [App (h1,a1)] where [h1] is a variable and
 * another term [t2], generate an LLambda substitution for [h1] if this is
 * possible, making whatever pruning and raising substitution that are
 * necessary to variables appearing within [t2].
 *
 * [t2] is assumed to be in head normal form, [h1] and [a1] are assumed to be
 * dereferenced.
 *
 * Exceptions can be raised from this code if there is
 *  - a non LLambda situation or
 *  - a failure in unification or
 *  - a type mismatch (if an a priori type checking has not been done).
 *
 * The unification computation is split into two parts, one that
 * examines the top level structure of [t2] and the other that descends
 * into its nested subparts. This organization is useful primarily
 * because [h1], the variable head of the first term can appear at the
 * toplevel in t2 without sacrificing unifiability but not in a nested
 * part. *)
let makesubst h1 t2 a1 =
  let n = List.length a1 in
  (* Check that h1 is a variable, get its timestamps *)
  let v1,ts1,lts1 = match observe h1 with
    | True | False
    | Binop _ | Binder _ ->
        fat h1
    | Var v -> assert (v.tag=instantiatable) ; v,v.ts,v.lts
    | _ -> assert false
  in
  let a1 = List.map Norm.hnorm a1 in

  (* Generating a substitution term and performing raising and
   * pruning substitutions corresponding to a non top-level
   * (sub)term. In this case the variable being bound cannot appear
   * embedded inside the term. This code assumes that its term
   * argument is head normalized. Exceptions can be
   * raised if unification fails or if LLambda conditions are found
   * to be violated. *)
  let rec nested_subst c lev =
    match observe c with
      | True | False
      | Binop _ | Binder _ ->
          fat c
      | QString _ | Nat _ -> c
      | Var v when constant v.tag ->
          (* Can [h1] depend on [c] ?
           * If so, the substitution is [c] itself, and the llambda restriction
           * ensures that this is the only solution.
           * If not, [c] must belong to the argument list. *)
          if v.ts <= ts1 && v.lts <= lts1 then c else
            let j = cindex v a1 n in
              if j = 0 then raise OccursCheck ;
              db (j+lev)
      | NB i ->
          if i <= lts1 then c else
            let j = nbindex i a1 n in
              if j = 0 then raise OccursCheck ;
              db (j+lev)
      | DB i ->
          if i <= lev then c else
            let j = bvindex (i-lev) a1 n in
              if j = 0 then raise OccursCheck ;
              db (j+lev)
      | Var v2 when variable v2.tag ->
          if eq c h1 then raise OccursCheck ;
          let (changed,a1',a2') = raise_and_invert v1 v2 a1 [] lev in
            if changed || not (lts1 >= v2.lts && (isLeft || ts1 >= v2.ts)) then
              let h'= fresh ~lts:(min lts1 v2.lts) ~ts:(min ts1 v2.ts) in
                bind c (app h' a2') ;
                app h' a1'
            else
              app c a1'
      | Lam (n,t) ->
          lambda n (nested_subst t (lev+n))
      | App (h2,a2) ->
          begin match observe h2 with
            | True | False
            | Binop _ | Binder _ ->
                fat h2
            | Var {tag=tag} when constant tag ->
                app
                  (nested_subst h2 lev)
                  (List.map (fun x -> nested_subst (Norm.hnorm x) lev) a2)
            | QString _
            | Nat _
            | DB _ | NB _ ->
                app
                  (nested_subst h2 lev)
                  (List.map (fun x -> nested_subst (Norm.hnorm x) lev) a2)
            | Var v2 when variable v2.tag ->
                if eq h2 h1 then raise OccursCheck ;
                let a2 = List.map Norm.hnorm a2 in
                let ts2,lts2 = v2.ts,v2.lts in
                check_flex_args a2 ts2 lts2 ;
                let changed,a1',a2' = raise_and_invert v1 v2 a1 a2 lev in
                  if changed then
                    let h' = fresh ~lts:(min lts1 v2.lts) ~ts:(min ts1 ts2) in
                      bind h2
                        (lambda (List.length a2) (app h' a2')) ;
                      app h' a1'
                  else
                    if not (lts1 >= lts2 && (isLeft || ts1 >= ts2)) then
                      let h' = fresh ~lts:(min lts1 v2.lts) ~ts:ts1 in
                        bind h2 h' ;
                        app h' a1'
                    else
                      app h2 a1'
            | Var _ -> failwith "logic variable on the left"
            | Ptr _
            | Susp _
            | App _
            | Lam _ -> assert false
          end
      | Var _ -> failwith "logic variable on the left"
      | _ -> assert false
  in

  (* Processing toplevel structure in generating a substitution.
   * First descend under abstractions. Then if the term is a
   * variable, generate the simple substitution. Alternatively, if
   * it is an application with the variable being bound as its head,
   * then generate the pruning substitution. In all other cases,
   * pass the task on to nested_subst. An optimization is possible
   * in the case that the term being examined has no outer
   * abstractions (i.e. lev = 0) and its head is a variable with a
   * time stamp greater than that of the variable being bound. In
   * this case it may be better to invoke raise_and_invert
   * directly with the order of the "terms" reversed.
   *
   * The incoming term is assumed to be head normalized. *)

  let rec toplevel_subst t2 lev =
    match observe t2 with
      | True | False
      | Binop _ | Binder _ ->
          fat t2
      | Lam (n,t2) -> toplevel_subst t2 (lev+n)
      | Var v2 when variable v2.tag ->
          if h1=t2 then
            if n=0 && lev=0 then h1 else raise TypesMismatch
          else begin
            if not (lts1 >= v2.lts && (isLeft || (ts1 >= v2.ts))) then
              bind t2
                (fresh ~lts:(min lts1 v2.lts) ~ts:(min ts1 v2.ts)) ;
            lambda (lev+n) t2
          end
      (* TODO the following seems harmless, and is sometimes useful..
      | Var v2 when not (constant v2.tag) && a1=[] ->
          lambda lev t2 (* [n] is 0 *)
      *)
      | App (h2,a2) ->
          begin match observe h2 with
            | True | False
            | Binop _ | Binder _ ->
                fat h2
            | QString _ | Nat _ ->
                let a2 = List.map Norm.hnorm a2 in
                check_flex_args a2 0 0 ;
                let bindlen = n+lev in
                if bindlen = List.length a2 then
                  let h1' = fresh ~lts:lts1 ~ts:ts1 in
                  let args = prune_same_var a1 a2 lev bindlen in
                  lambda bindlen (app h1' args)
                else
                  raise TypesMismatch
            | Var {ts=ts2;lts=lts2} when eq h1 h2 ->
                (* [h1] being instantiatable, no need to check it for [h2] *)
                let a2 = List.map Norm.hnorm a2 in
                check_flex_args a2 ts2 lts2 ;
                let bindlen = n+lev in
                if bindlen = List.length a2 then
                  let h1' = fresh ~lts:lts1 ~ts:ts1 in
                  let args = prune_same_var a1 a2 lev bindlen in
                  lambda bindlen (app h1' args)
                else
                  raise TypesMismatch
            | App _ | Lam _
            | Var _ | DB _ | NB _ ->
                lambda (n+lev) (nested_subst t2 lev)
            | Susp _ | Ptr _ -> assert false
          end
      | Ptr _ -> assert false
      | _ -> lambda (n+lev) (nested_subst t2 lev)
  in

  try
    check_flex_args a1 ts1 lts1 ;
    toplevel_subst t2 0
  with
    | NotLLambda e ->
        (* Not a pattern: try a very strict occurs-check to allow
         * simple cases of the form v1=t2. *)
        if a1 = [] && (can_bind v1 t2) then
          t2
        else
          not_ll e


(* Unifying the arguments of two rigid terms with the same head, these
 * arguments being given as lists. Exceptions are raised if
 * unification fails or if there are unequal numbers of arguments; the
 * latter will not arise if type checking has been done. *)
let rec unify_list l1 l2 =
  try
    List.iter2 (fun a1 a2 -> unify (Norm.hnorm a1) (Norm.hnorm a2)) l1 l2
  with
    | Invalid_argument _ -> raise TypesMismatch

(* [unify_const_term cst t2] unify [cst=t2], assuming that [cst] is a constant.
 * Fail if [t2] is a variable or an application.
 * If it is a lambda, binders need to be equalized and so this becomes
 * an application-term unification problem. *)
and unify_const_term cst t2 = if eq cst t2 then () else
  match observe t2 with
    | Lam (n,t2) ->
        let a1 = lift_args [] n in
          unify_app_term cst a1 (app cst a1) t2
    | Var {tag=t} when not (variable t || constant t) ->
        failwith "logic variable on the left"
    | True | False
    | Binop _ | Binder _ ->
        fat t2
    | _ -> raise (ConstClash (cst,t2))

(* Unifying the bound variable [t1] with [t2].
 * Fail if [t2] is a variable, an application or a constant.
 * If it is a lambda, binders need to be
 * equalized and this becomes an application-term unification problem. *)
and unify_bv_term n1 t1 t2 = match observe t2 with
  | DB n2 ->
      if n1<>n2 then raise (ConstClash (t1,t2))
  | NB n2 ->
      raise (ConstClash (t1,t2))
  | Lam (n,t2)  ->
      let t1' = lift t1 n in
      let a1 = lift_args [] n in
        unify_app_term t1' a1 (app t1' a1) t2
  | Var {tag=t} when not (variable t || constant t) ->
      failwith "logic variable on the left"
  | True | False
  | Binop _ | Binder _ ->
      fat t2
  | _ -> assert false

(* Unifying the nabla variable [t1] with [t2]. *)
and unify_nv_term n1 t1 t2 = match observe t2 with
  | NB n2 ->
      if n1<>n2 then raise (ConstClash (t1,t2))
  | DB n2 ->
      raise (ConstClash (t1,t2))
  | Lam (n,t2) ->
      let a1 = lift_args [] n in
        unify_app_term t1 a1 (app t1 a1) t2
  | Var {tag=t} when not (variable t || constant t) ->
      failwith "logic variable on the left"
  | True | False
  | Binop _ | Binder _ ->
      fat t2
  | _ -> assert false

(* [unify_app_term h1 a1 t1 t2] unify [App h1 a1 = t2].
 * [t1] should be the term decomposed as [App h1 a1].
 * [t2] should be dereferenced and head-normalized, different from a var. *)
and unify_app_term h1 a1 t1 t2 = match observe h1,observe t2 with
  | Var {tag=tag}, _ when variable tag ->
      bind h1 (makesubst h1 t2 a1)
  | QString s1, App (h2,a2) ->
      begin match observe h2 with
        | QString s2 ->
            if s1=s2 then
              unify_list a1 a2
            else
              raise (ConstClash (h1,h2))
        | Nat _ ->
            raise (ConstClash (h1,h2))
        | Var {tag=tag} when constant tag ->
            raise (ConstClash (h1,h2))
        | DB _ | NB _ ->
            raise (ConstClash (h1,h2))
        | Var {tag=tag} when variable tag ->
            bind h2 (makesubst h2 t1 a2)
        | Var {tag=t} ->
            failwith "logic variable on the left"
        | _ -> assert false
      end
  | Nat i, App (h2,a2) ->
      begin match observe h2 with
        | QString _ ->
            raise (ConstClash (h1,h2))
        | Nat j ->
            if i=j then
              unify_list a1 a2
            else
              raise (ConstClash (h1,h2))
        | Var {tag=tag} when constant tag ->
            raise (ConstClash (h1,h2))
        | DB _ | NB _ ->
            raise (ConstClash (h1,h2))
        | Var {tag=tag} when variable tag ->
            bind h2 (makesubst h2 t1 a2)
        | Var {tag=t} ->
            failwith "logic variable on the left"
        | _ -> assert false
      end
  | Var {tag=tag}, App (h2,a2) when constant tag ->
      begin match observe h2 with
        | QString _ | Nat _ ->
            raise (ConstClash (h1,h2))
        | Var {tag=tag} when constant tag ->
            if eq h1 h2 then
              unify_list a1 a2
            else
              raise (ConstClash (h1,h2))
        | DB _ | NB _ ->
            raise (ConstClash (h1,h2))
        | Var {tag=tag} when variable tag ->
            bind h2 (makesubst h2 t1 a2)
        | Var {tag=t} ->
            failwith "logic variable on the left"
        | _ -> assert false
      end
  | NB n1, App (h2,a2) ->
      begin match observe h2 with
        | QString _ | Nat _ | DB _ -> raise (ConstClash (h1,h2))
        | NB n2 ->
            if n1=n2 then unify_list a1 a2 else raise (ConstClash (h1,h2))
        | Var v ->
            if constant v.tag then
              raise (ConstClash (h1,h2))
            else if variable v.tag then
              bind h2 (makesubst h2 t1 a2)
            else
              failwith "logic variable on the left"
        | _ -> assert false
      end
  | DB n1, App (h2,a2) ->
      begin match observe h2 with
        | QString _ | Nat _ | NB _ -> raise (ConstClash (h1,h2))
        | DB n2 ->
            if n1=n2 then unify_list a1 a2 else raise (ConstClash (h1,h2))
        | Var v ->
            if constant v.tag then
              raise (ConstClash (h1,h2))
            else if variable v.tag then
              bind h2 (makesubst h2 t1 a2)
            else
              failwith "logic variable on the left"
        | _ -> assert false
      end
  | _, Lam (n,t2) ->
      let h1' = lift h1 n in
      let a1' = lift_args a1 n in
      let t1' = app h1' a1' in
        unify_app_term h1' a1' t1' t2
  | Ptr  _, _ | _, Ptr  _
  | Susp _, _ | _, Susp _ -> assert false
  | _, Var {tag=t}
  | Var {tag=t}, _ when not (variable t || constant t) ->
      failwith "logic variable on the left"
  | True,_ | False,_
  | Binop _,_ | Binder _,_ -> fat t1
  | _,True | _,False
  | _,Binop _ | _,Binder _ -> fat t2
  | _ -> raise (ConstClash (h1,t2))

(* The main unification procedure.
 * Either succeeds and realizes the unification substitutions as side effects
 * or raises an exception to indicate nonunifiability or to signal
 * a case outside of the LLambda subset. When an exception is raised,
 * it is necessary to catch this and at least undo bindings for
 * variables made in the attempt to unify. This has not been included
 * in the code at present.
 *
 * This procedure assumes that the two terms it gets are in
 * head normal form and that there are no iterated
 * lambdas or applications at the top level. Any necessary adjustment
 * of binders through the eta rule is done on the fly. *)
and unify t1 t2 = match observe t1,observe t2 with
  | Var {tag=t},_ when variable t -> bind t1 (makesubst t1 t2 [])
  | _,Var {tag=t} when variable t -> bind t2 (makesubst t2 t1 [])
  | App (h1,a1),_                 -> unify_app_term h1 a1 t1 t2
  | _,App (h2,a2)                 -> unify_app_term h2 a2 t2 t1
  | True,_ | False,_
  | Binop _,_ | Binder _,_        -> fat t1
  | _,True | _,False
  | _,Binop _ | _,Binder _        -> fat t2
  | QString _,_ | Nat _,_         -> unify_const_term t1 t2
  | _,QString _ | _,Nat _         -> unify_const_term t2 t1
  | Var {tag=t},_ when constant t -> unify_const_term t1 t2
  | _,Var {tag=t} when constant t -> unify_const_term t2 t1
  | DB n,_                        -> unify_bv_term n t1 t2
  | _,DB n                        -> unify_bv_term n t2 t1
  | NB n,_                        -> unify_nv_term n t1 t2
  | _,NB n                        -> unify_nv_term n t2 t1
  | Lam (n1,t1),Lam(n2,t2)   ->
      if n1>n2 then
        unify (lambda (n1-n2) t1) t2
      else
        unify t1 (lambda (n2-n1) t2)
  | _ -> failwith "logic variable on the left"

let pattern_unify t1 t2 = unify (Norm.hnorm t1) (Norm.hnorm t2)

end
