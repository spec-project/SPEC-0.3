(****************************************************************************)
(* An implementation of Higher-Order Pattern Unification                    *)
(* Copyright (C) 2006-2012 Nadathur, Linnell, Baelde, Ziegler, Gacek, Heath *)
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

open Term
open Format

exception Found of int

let debug = ref false

let string_of_tag = function
  | Eigen -> "e"
  | Constant -> "c"
  | Logic -> "l"

let string_of_binder = function
  | Forall -> "forall"
  | Exists -> "exists"
  | Nabla -> "nabla"

let string_of_binop = function
  | Eq -> "="
  | And -> "/\\"
  | Or -> "\\/"
  | Arrow -> "->"

let priorities = function
  | Eq -> 5,4,5
  | And -> 3,3,3
  | Or -> 2,2,2
  | Arrow -> 2,1,1

(* [assoc], [infix], [set_infix], [is_infix], [get_assoc] and [priority]
 * are commented out until we add real support for
 * runtime-defined syntactic behaviours,
 * ie [#infix pred.] or such.

type assoc = Left | Right | Both | Nonassoc

(* List of infix operators sorted by priority. *)
let infix : (string * assoc) list ref = ref []
let set_infix l = infix := l
let is_infix x = List.mem_assoc x !infix
let get_assoc op = List.assoc op !infix
let priority x =
  try
    ignore (List.fold_left
              (fun i (e, assoc) -> if e = x then raise (Found i) else i+1)
              1 !infix) ;
    0
  with
    | Found i -> i
let get_max_priority () = List.length !infix *)
(* XXX This, and the inline hard-coded priorities of the logical connectives,
 * has to change. We may not be able to link the pprint priority
 * to the parser precedence, but still... *)
let get_max_priority () = 4

(* Utility to get a 'to_string' from a 'print' *)
let formatter,do_formatter =
  let buf = Buffer.create 20 in
  let chan = formatter_of_buffer buf in
    chan,
    (fun f ->
       assert (Buffer.length buf = 0) ;
       f () ;
       pp_print_flush chan () ;
       assert (Buffer.length buf > 0) ;
       let s = Buffer.contents buf in
       Buffer.clear buf ;
       s)

(* Print a term. Ensures consistent namings, using naming hints when available.
 * Behaves consistently from one call to another unless Term.reset_namespace
 * is called between executions.
 * Two lists of names must be passed for free "bound variables"
 * and generic variables. These names are assumed not to conflict with any
 * other name. The good way to ensure that is to use Term.get_dummy_name and
 * [Term.free].
 * The input term should be fully normalized. *)
let print_full ~generic ~bound chan term =
  let get_nth list n s =
    try
      List.nth list n
    with
      Failure _ -> s
  in

  let high_pr = 1 + get_max_priority () in
  let rec pp ~bound pr chan term =
    match observe term with
      | Var v ->
          let name = get_name term in
          if !debug then
            fprintf chan "%s[%d/%d/%s]"
              name v.ts v.lts (string_of_tag v.tag)
          else
            fprintf chan "%s" name
      | NB i ->
          fprintf chan "%s"
            (get_nth generic (i-1) ("nabla(" ^ (string_of_int (i - 1)) ^ ")"))
      | DB i ->
          fprintf chan "%s"
            (get_nth bound (i-1) ("db(" ^ (string_of_int i) ^ ")"))
      | QString s -> fprintf chan "%S" s
      | Nat i -> fprintf chan "%d" i
      | True -> fprintf chan "true"
      | False -> fprintf chan "false"
      | Binop (b,t1,t2) ->
          let pr_left,pr_op,pr_right = priorities b in
          let print =
            if pr_op >= pr then
              fprintf chan "@[%a@ %s@ %a@]"
            else
              fprintf chan "@[<1>(%a@ %s@ %a)@]"
          in
          print
            (pp ~bound pr_left) t1
            (string_of_binop b)
            (pp ~bound pr_right) t2
      | Binder (b,i,t) ->
          assert (i>0) ;
          (* Get [i] more dummy names for the new bound variables.
           * Release them after the printing of this term. *)
          let more = get_dummy_names ~start:1 i "x" in
          let head = String.concat " " more in
          let print =
            if pr=0 then
              fprintf chan "@[<2>%s@ %s,@ %a@]"
             else
              fprintf chan "@[<3>(%s@ %s,@ %a)@]"
          in
          print
            (string_of_binder b)
            head
            (pp ~bound:(List.rev_append more bound) 0) t ;
          List.iter free more
      | App (t,ts) ->
          begin match (observe t, ts) with
            (*| Var {tag=Constant}, [a; b] when is_infix (get_name t) ->
                let op = get_name t in
                let op_p = priority op in
                let assoc = get_assoc op in
                let pr_left, pr_right = match assoc with
                  | Left -> op_p, op_p+1
                  | Right -> op_p+1, op_p
                  | Both -> op_p, op_p
                  | Nonassoc -> op_p+1, op_p+1
                in
                let print =
                  if op_p >= pr then
                    fprintf chan "@[%a@ %s@ %a@]"
                  else
                    fprintf chan "@[<1>(%a@ %s@ %a)@]"
                in
                print (pp ~bound pr_left) a op (pp ~bound pr_right) b*)
            | _,hd::tl ->
                let print =
                  if pr=0 then
                    fprintf chan "@[<2>%a %a%a@]"
                   else
                    fprintf chan "@[<3>(%a %a%a)@]"
                in
                print

                  (pp ~bound high_pr) t
                  (pp ~bound high_pr) hd
                  (fun chan ->
                     List.iter
                       (fprintf chan "@ %a" (pp ~bound high_pr)))
                  tl
            | _,[] -> pp ~bound pr chan t
          end
      | Lam (i,t) ->
          assert (i>0) ;
          (* Get [i] more dummy names for the new bound variables.
           * Release them after the printing of this term. *)
          let more = get_dummy_names ~start:1 i "x" in
          let head = String.concat "\\" more in
          let print =
            if pr=0 then
              fprintf chan "%s\\@ %a"
            else
              fprintf chan "@[<1>(%s\\@ %a)@]"
          in
          print head (pp ~bound:(List.rev_append more bound) 0) t ;
          List.iter free more
      | Susp (t,ol,_,_) ->
          fprintf chan "<%d:%a>" ol (pp ~bound pr) t
      | Ptr  _ -> assert false (* observe *)
  in
  fprintf chan "@[%a@]" (pp ~bound 0) term

let term_to_string_full ~generic ~bound tm =
  do_formatter (fun () -> print_full ~generic ~bound formatter tm)

let term_to_string_full_debug ~generic ~bound dbg term =
  let debug' = !debug in
  let s =
    debug := dbg ;
    term_to_string_full ~generic ~bound term
  in
  debug := debug';
  s

let get_generic_names x =
  let nbs = get_nablas x in
  let max_nb = List.fold_left max 0 nbs in
  get_dummy_names ~start:1 max_nb "n"

let print ?(bound=[]) chan term =
  let term = Norm.deep_norm term in
  let generic = get_generic_names term in
  let s = print_full ~generic ~bound chan term in
  List.iter free generic ;
  s

let term_to_string ?(bound=[]) tm =
  do_formatter (fun () -> print ~bound formatter tm)

let pp_term out term = print out term

let print_term ?(bound=[]) term =
  print ~bound std_formatter term

(* Utility for tools such as Taci which push down formula-level abstractions
 * to term level abstractions. Dummy names should be created (and freed)
 * during the printing of the formula, and passed as the bound names to this
 * function, which won't display the lambda prefix.
 * The input term should have at least [List.length bound] abstractions
 * at toplevel. *)
let pp_preabstracted ~generic ~bound chan term =
  (* let term = Norm.hnorm term in *)
  let len = List.length bound in
  match observe term with
    | Lam (n,term) ->
        assert (len <= n) ;
        print_full ~generic ~bound chan (lambda (n-len) term)
    | _ ->
        (* assert (bound = []); *)
        print_full ~generic ~bound chan term

let term_to_string_preabstracted ~generic ~bound term =
  do_formatter (fun () -> pp_preabstracted ~generic ~bound formatter term)
