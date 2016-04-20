(****************************************************************************)
(* An implementation of Higher-Order Pattern Unification                    *)
(* Copyright (C) 2006-2012 Nadathur, Linnell, Baelde, Ziegler, Gacek, Tiu,  *)
(*                         Heath                                            *)
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

(* Representation of higher-order terms. *)

type tag = Eigen | Constant | Logic

(* Physical equality is used to distinguish variables. *)
type var = {
  id  : int ; (* Only used for hashing *)
  tag : tag ;
  ts  : int ; (* Always zero for constants in Bedwyr *)
  lts : int
}

type binder = Forall | Exists | Nabla
type binop = Eq | And | Or | Arrow

(* TODO ? phantom type for annotating term with what's inside
 * [ `Var ] term, etc... *)
type term = rawterm
and rawterm =
  | QString of string
  | Nat    of int
  | Var    of var (* Only when "observing" the term *)
  | DB     of int
  | NB     of int (* Nabla variables *)
  | True
  | False
  | Binop  of binop * term * term
  | Binder of binder * int * term
  | Lam    of int * term
  | App    of term * term list
  | Susp   of term * int * int * env
  | Ptr    of ptr
and ptr = in_ptr ref
and in_ptr = V of var | T of term
and env = envitem list
and envitem = Dum of int | Binding of term * int

(* Creating terms *)

let rec observe = function
  | Ptr {contents=T d} -> observe d
  | Ptr {contents=V v} -> Var v
  | t -> t

let rec deref = function
  | Ptr {contents=T t} -> deref t
  | t -> t

let qstring s = QString s
let nat i = assert (i>=0) ; Nat i
let db n = DB n
let nabla n = NB n
let op_true = True
let op_false = False
let op_binop b t1 t2 = Binop (b,t1,t2)
let op_eq = op_binop Eq
let op_and = op_binop And
let op_or = op_binop Or
let op_arrow = op_binop Arrow

(* Add [n] times quantifier [b] *)
let binder b n t =
  assert (n>=0) ;
  if n=0 then t else
    let rec aux n t =
      match deref t with
        | Binder (b',n',t) when b=b' -> aux (n+n') t
        | _ -> Binder (b,n,t)
    in
    aux n t

(* Add [n] abstractions. *)
let lambda n t =
  assert (n>=0) ;
  if n=0 then t else
    let rec aux n t =
      match deref t with
        | Lam (n',t') -> aux (n+n') t'
        | _ -> Lam (n,t)
    in
    aux n t

let app a b = if b = [] then a else match observe a with
  | App(a,c) -> App (a,c @ b)
  | _ -> App (a,b)

let susp t ol nl e = Susp (t,ol,nl,e)

(* Term equalities *)

exception NonNormalTerm

(* Fast observational equality; no normalization is peformed. *)
let rec eq t1 t2 =
  match t1,t2 with
    (* Compare leafs *)
    | _,_ when t1=t2 -> true
    | DB i1, DB i2
    | NB i1, NB i2 -> i1=i2
    | Ptr {contents=V v1}, Ptr {contents=V v2} -> v1==v2
    (* Ignore Ptr. It's an implementation artifact *)
    | _, Ptr {contents=T t2} -> eq t1 t2
    | Ptr {contents=T t1}, _ -> eq t1 t2
    (* Propagation *)
    | Binop (b1,t1,t1'), Binop (b2,t2,t2') ->
        b1 = b2 && eq t1 t2 && eq t1' t2'
    | Binder (b1,n1,t1), Binder (b2,n2,t2) ->
        b1 = b2 && n1 = n2 && eq t1 t2
    | App (h1,l1), App (h2,l2) ->
        List.length l1 = List.length l2 &&
        List.fold_left2
          (fun test t1 t2 -> test && eq t1 t2)
          true (h1::l1) (h2::l2)
    | Lam (n1,t1), Lam (n2,t2) ->
        n1 = n2 && eq t1 t2
    | Var _, _ | _, Var _ -> assert false
    | Susp (t,ol,nl,e), Susp (tt,oll,nll,ee) ->
        ol = oll && nl = nll && eq t tt &&
          List.fold_left2
            (fun test e1 e2 ->
               test && match e1,e2 with
                 | Dum i, Dum j when i = j -> true
                 | Binding (t,i), Binding (tt,j) when i=j && eq t tt -> true
                 | _ -> false)
            true e ee
    | _ -> false

(* Equivariant checking *)
let eqvt t1 t2 =
  let bindings = ref [] in
  let rec aux s1 s2 =
    match s1,s2 with
      | _,_ when t1=t2 -> true
      | DB i1, DB i2 -> i1=i2
      | NB i1, NB i2 ->
          let bd = try Some (List.find (fun (x,y) -> x=i1) !bindings)
          with Not_found -> None
          in
          begin match bd with
            | Some (x,y) -> (y = i2)
            | None -> (bindings := (i1,i2)::!bindings ; true)
          end
      | Ptr {contents=V v1}, Ptr {contents=V v2} -> v1==v2
      | _, Ptr {contents=T t2} -> aux s1 t2
      | Ptr {contents=T t1}, _ -> aux t1 s2
      (* Propagation *)
      | Binop (b1,t1,t1'), Binop (b2,t2,t2') ->
          b1 = b2 && aux t1 t2 && aux t1' t2'
      | Binder (b1,n1,t1), Binder (b2,n2,t2) ->
          b1 = b2 && n1 = n2 && aux t1 t2
      | App (h1,l1), App (h2,l2) ->
          List.length l1 = List.length l2 &&
          List.fold_left2
            (fun test t1 t2 -> test && aux t1 t2)
            true (h1::l1) (h2::l2)
      | Lam (n1,t1), Lam (n2,t2) ->
          n1 = n2 && aux t1 t2
      | Var _, _ | _, Var _ -> assert false
      | Susp _, _ -> raise NonNormalTerm
      | _ -> false
  in
  aux t1 t2

(* Creating and extracting variables *)

(* [var_names] is used to attach a naming hint for the pretty printer
 * to variables, not only those built by the parser. It is designed to not
 * interfere with the GC. *)
module Hint = struct
  module M = Map.Make(struct type t = int let compare = compare end)
  let var_names = ref M.empty
  let add var name =
    var_names := M.add var.id name !var_names ;
    (* TODO define the finalization function before,
     * when [var] isn't defined? *)
    Gc.finalise (fun v -> var_names := M.remove v.id !var_names) var
  let find var =
    M.find var.id !var_names
end

let fresh_id =
  let c = ref 0 in
    fun () -> incr c ; !c

(* Generate a fresh variable, attach a naming hint to it. *)
let fresh ?name ~lts ~ts tag =
  let v = {id=fresh_id();tag=tag;ts=ts;lts=lts} in
  begin match name with
    | Some name -> Hint.add v name
    | None -> ()
  end ;
  Ptr (ref (V v))

let get_var x = match observe x with
  | Var v -> v
  | _ -> assert false

(* Binding variables *)

(* Binding a variable to a term. The *contents* of the cell representing the
 * variable is a reference which must be updated. Also the variable must
 * not be made a reference to itself. This can be changed to mimic the
 * Prolog representation of bound variables but then deref will have to
 * work differently. This is the place to introduce trailing. *)

type state = int
let bind_stack = Stack.create ()
let bind_len = ref 0

let save_state () = !bind_len

let restore_state n =
  assert (n <= !bind_len) ;
  for i = 1 to !bind_len-n do
    let (v,contents) = Stack.pop bind_stack in
    v := contents
  done ;
  bind_len := n

type subst = (ptr*in_ptr) list
type unsubst = subst

let bind v t =
  let dv = match deref v with
    | Ptr t -> t
    | _ -> assert false (* [v] should represent a variable *)
  in
  let dt = deref t in
  if match dt with Ptr r when r==dv -> false | _ -> true then begin
    Stack.push (dv,!dv) bind_stack ;
    dv := T dt ;
    incr bind_len
  end

exception Done

let get_subst state =
  let subst = ref [] in
  let count = ref (!bind_len-state) in
  assert (!count >= 0) ;
  try
    Stack.iter
      (fun (v,_) ->
         if !count = 0 then raise Done ;
         subst := (v,!v)::!subst ;
         decr count)
      bind_stack ;
    !subst
  with Done -> !subst

let apply_subst s = List.fold_left (fun sub (v,contents) ->
                                      let old = !v in
                                        v := contents ;
                                        (v,old)::sub) [] s

let undo_subst = List.iter (fun (s,old) -> s:=old)

let eq_ptr s t =
  match s,t with
    | (V x),(V y) when x==y -> true
    | (T u),(T v) -> eq u v
    | _ -> false

(* Check if two substitutions are equal *)
let eq_subst sub1 sub2 =
  let rec aux s1 s2 =
    match s1 with
      | [] -> true
      | ((v,c)::rest) ->
          let (_,d) = (List.find (fun (x,y) -> v==x)) s2 in
          if (eq_ptr c d) then (aux rest s2) else false
  in
  try (aux sub1 sub2 && aux sub2 sub1)
  with Not_found -> false

(* Handling variable names *)

module NS = Map.Make(struct type t = string let compare = compare end)
type namespace = term NS.t

(* [symbols] is used to obtain the exact same variable term for
 * representing all occurrences of that variable -- used by the parser. *)
let symbols = ref NS.empty

let save_namespace () = !symbols
let restore_namespace s = symbols := s

(* Get the unique variable attached to that name, preserving sharing.
 * The variable is created if it does not exist. *)
let get_var_by_name ~tag ~ts ~lts name =
  try NS.find name !symbols
  with Not_found ->
    assert (name <> "") ;
    let lts = 0 in
    let t = fresh tag ~ts ~lts ~name in
    symbols := NS.add name t !symbols ;
    t

(* Same as [get_var_by_name] but infers the tag from the name and sets both
 * levels to 0. *)
let atom ?tag name =
  let tag = match tag with
    | Some tag -> tag
    | None ->
        begin match name.[0] with
          | 'A'..'Z' -> Logic
          | _ -> Constant
        end
  in
  if name = "_"
  then fresh Logic ~ts:0 ~lts:0
  else get_var_by_name ~ts:0 ~lts:0 ~tag name

(* @return the naming hint attached to the variable,
 * or a default hint if there is none *)
let get_var_name v =
  try Hint.find v
  with Not_found -> "_"

(* @return the naming hint attached to the variable,
 * or a default hint if there is none *)
let get_hint v =
  try Hint.find v
  with Not_found ->
    begin match v.tag with
      | Logic -> "H"
      | Eigen -> "h"
      | Constant -> "c"
    end

(* @return the name of the variable,
 * or a naming hint attached to it *)
let get_var_unique_name v =
  let prefix = get_hint v in
  let rec lookup suffix =
    let name = if suffix < 0 then prefix else prefix ^ string_of_int suffix in
    if NS.mem name !symbols
    then lookup (suffix+1)
    else name
  in
  lookup (-1)

(* Find an unique name for [v] (based on a naming hint if there is one)
 * and registers it in the symbols table. *)
let get_name t =
  let t = deref t in
  let existing_name =
    NS.fold
      (fun key value x ->
         (* Do NOT use [eq] instead of [=] here, otherwise it will follow
          * references -- notice that the term in the table has been changed by
          * bindings too.
          * Suppose you bind Y to 1,
          * the initial value representing Y would be [eq] to 1,
          * and could thus take the name 1, depending on the order in which the
          * table is traversed. *)
         if value = t then Some key else x)
      !symbols
      None
  in
  match existing_name with
    | Some n -> n
    | None ->
        let v = get_var t in
        let name = get_var_unique_name v in
        symbols := NS.add name t !symbols ;
        name

let dummy = let n = -1 in Ptr(ref(V { id=n;ts=n;lts=n;tag=Constant }))

(* [get_dummy_name prefix] finds a free name starting with [prefix] and
 * registers it. If [start] is not provided, the attempted suffixes will be
 * "", "0", "1", etc. If it is provided it will be used as the first suffix to
 * try. *)
let get_dummy_name ?(start=(-1)) prefix =
  let rec lookup suffix =
    let name =
      if suffix < 0 then prefix else prefix ^ string_of_int suffix
    in
    if NS.mem name !symbols then
      lookup (suffix+1)
    else begin
      symbols := NS.add name dummy !symbols ;
      name
    end
  in
  lookup start

(* List of [n] new dummy names, most recent first. *)
let get_dummy_names ?(start=(-1)) n prefix =
  let rec aux i =
    if i=0 then [] else
      let tl = aux (i-1) in
      (get_dummy_name ~start prefix)::tl
  in
  List.rev (aux n)

let is_free name =
  not (NS.mem name !symbols)

let free n =
  symbols := NS.remove n !symbols

(* Copying *)

(* [copy_eigen ()] instantiates a copier, that copies terms,
 * preserving sharing inside the set of copied terms.
 * Input terms should be normalized. *)
let copy_eigen () =
  let tbl = Hashtbl.create 100 in
  fun ?(passive=false) tm ->
    let rec cp tm = match observe tm with
      | Var v when v.tag = Eigen ->
          begin try Hashtbl.find tbl v with
            | Not_found ->
                if passive then tm else
                  let v' = { v with id = fresh_id () } in
                  let x = Ptr (ref (V v')) in
                    begin try Hint.add v' (Hint.find v) with _ -> () end ;
                    Hashtbl.add tbl v x ;
                    x
          end
      | Var v -> tm
      | Binop (b,t1,t2) -> Binop (b,cp t1,cp t2)
      | Binder (b,l,t) -> Binder (b,l,cp t)
      | App (a,l) -> App (cp a, List.map cp l)
      | Lam (l,b) -> Lam (l,cp b)
      | QString _ | Nat _ | DB _ | NB _ | True | False as x -> x
      | Susp _ | Ptr _ -> assert false
    in
    cp tm

(* copying a term: No sharing is maintained, except possibly on
   pointers to variables. *)
let rec simple_copy tm =
  match tm with
    | QString _ | Nat _ | DB _ | NB _ | True | False | Var _ | Ptr {contents=V _} -> tm
    | Binop (b,t1,t2) -> Binop (b,simple_copy t1,simple_copy t2)
    | Binder (b,n,t) -> Binder (b,n,simple_copy t)
    | App (a,l) -> App (simple_copy a, List.map simple_copy l)
    | Lam (n,b) -> Lam (n,simple_copy b)
    | Ptr {contents=T t} -> simple_copy t
    | Susp _ -> assert false

(* copying a term maintaining shared structures *)
let shared_copy tm =
  let tbl = Hashtbl.create 100 in
  let rec cp t =
    match t with
      | QString _ | Nat _ | DB _ | NB _ | True | False | Var _ | Ptr {contents=V _} -> t
      | Binop (b,t1,t2) -> Binop (b,cp t1,cp t2)
      | Binder (b,n,t) -> Binder (b,n,cp t)
      | App (a,l) -> App (cp a, List.map cp l)
      | Lam (n,b) -> Lam (n,cp b)
      | Ptr ({contents=T s} as x) ->
          begin try Hashtbl.find tbl x  with
            | Not_found ->
                let v = Ptr {contents=T (cp s)} in
                Hashtbl.add tbl x v ;
                v
          end
      | Susp _ -> assert false
  in
   cp tm

(* Abstracting *)

(* [pre_abstract var t] computes the abstraction of [t] over [var],
 * which may be either a variable or a nabla index.
 * This function is not destructive and hence breaks the sharing. *)
let pre_abstract target t =
  match observe target with
    | Var target ->
        (* Recursively raise dB indices and abstract over [target]. *)
        let rec aux n t = match t with
          | NB i -> t
          | DB i -> if i>=n then DB (i+1) else t
          | QString _
          | Nat _
          | True
          | False -> t
          | Binop (b,t1,t2) -> Binop (b,aux n t1,aux n t2)
          | Binder (b,m,t) -> Binder (b,m,aux (n+m) t)
          | App (h,ts) ->
              App ((aux n h), (List.map (aux n) ts))
          | Lam (m,s) -> Lam (m, aux (n+m) s)
          | Ptr {contents=T t} -> Ptr {contents=T (aux n t)}
          | Ptr {contents=V v} -> if v==target then DB n else t
          | Var _ -> assert false
          | Susp _ -> raise NonNormalTerm
        in
        aux 1 t
    | NB target ->
        (* Recursively raise dB indices and abstract over [target]. *)
        let rec aux n t = match t with
          | NB i -> if i=target then DB n else t
          | DB i -> if i>=n then DB (i+1) else t
          | QString _
          | Nat _
          | True
          | False -> t
          | Binop (b,t1,t2) -> Binop (b,aux n t1,aux n t2)
          | Binder (b,m,t) -> Binder (b,m,aux (n+m) t)
          | App (h,ts) ->
              App ((aux n h), (List.map (aux n) ts))
          | Lam (m,s) -> Lam (m, aux (n+m) s)
          | Ptr {contents=T t} -> Ptr {contents=T (aux n t)}
          | Ptr {contents=V v} -> t
          | Var _ -> assert false
          | Susp _ -> raise NonNormalTerm
        in
        aux 1 t
    | _ -> assert false

(* [abstract var t] builds the abstraction computed by [pre_abstract var t]. *)
let abstract target t =
  lambda 1 (pre_abstract target t)

(* [quantify b var t] builds the b-quantification computed by [pre_abstract var t]. *)
let quantify b target t =
  binder b 1 (pre_abstract target t)

(* [abstract_flex var t] similar to abstract var t, but
 * will abstract flexible subterms headed by var. *)
let abstract_flex target t =
  match observe target with
    | Var target ->
        (* Recursively raise dB indices and abstract over [target]. *)
        let rec aux n t = match t with
          | NB i -> t
          | DB i -> if i>=n then DB (i+1) else t
          | QString _
          | Nat _
          | True
          | False -> t
          | Binop (b,t1,t2) -> Binop (b,aux n t1,aux n t2)
          | Binder (b,m,t) -> Binder (b,m,aux (n+m) t)
          | App (h,ts) ->
              begin match observe h with
                | Var v when v==target -> DB n
                | _ -> App ((aux n h), (List.map (aux n) ts))
              end
          | Lam (m,s) -> Lam (m, aux (n+m) s)
          | Ptr {contents=T t} -> Ptr {contents=T (aux n t)}
          | Ptr {contents=V v} -> if v==target then DB n else t
          | Var _ -> assert false
          | Susp _ -> raise NonNormalTerm
        in
        lambda 1 (aux 1 t)
    | _ -> assert false

(* Extract variable terms *)

(* [get_vars test ts] computes the list of variables [v] occuring in
 * the list of normalized terms [ts] and which satisfy [test v]. *)
let get_vars test ts =
  let rec fv l t = match observe t with
    | QString _ | Nat _ | DB _ | NB _ | True | False -> l
    | Var v ->
        if test v && not (List.mem_assq v l) then ((v,t)::l) else l
    | Binop (_,t1,t2) -> fv (fv l t1) t2
    | Binder (b,_,t) -> fv l t
    | App (h,ts) -> List.fold_left fv (fv l h) ts
    | Lam (_,t) -> fv l t
    | Susp _ | Ptr _ -> assert false
  in
  List.map snd (List.fold_left fv [] ts)

(* Logic variables of [ts], assuming that they are normalized. *)
let logic_vars = get_vars (fun v -> v.tag = Logic)

(* Eigen variables of [ts], assuming that they are normalized. *)
let eigen_vars = get_vars (fun v -> v.tag = Eigen)

(* [get_nablas x] computes the list of nabla variables [n] occuring in
 * the normalized term [x]. *)
let get_nablas x =
  let rec nb l t = match observe t with
    | QString _ | Nat _ | Var _ | DB _ | True | False -> l
    | NB i -> if List.mem i l then l else i::l
    | Binop (_,t1,t2) -> nb (nb l t1) t2
    | Binder (_,_,t) -> nb l t
    | App (hd,tl) -> List.fold_left nb (nb l hd) tl
    | Lam (_,t) -> nb l t
    | Susp _ | Ptr _ -> assert false
  in
  nb [] x

(* Convenience *)

module Notations =
struct
  let (%=) = eq
  let (!!) = observe
  let (//) = lambda
  let (^^) = app
end

let fresh_name name =
  let v = fresh ~name:name Constant ~lts:0 ~ts:0 in
  get_name v

let get_var_ts v = v.ts
let get_var_lts v = v.lts
