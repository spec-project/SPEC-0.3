(****************************************************************************)
(* An implementation of Higher-Order Pattern Unification                    *)
(* Copyright (C) 2006-2011 Nadathur, Linnell, Baelde, Ziegler, Gacek, Tiu,  *)
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

(** Representation of higher-order terms. *)

type tag = Eigen | Constant | Logic

(** Physical equality is used to distinguish variables. *)
type var = private {
  id  : int ; (** only used for hashing *)
  tag : tag ;
  ts  : int ; (** always zero for constants in Bedwyr *)
  lts : int
}

(** Quantifier: [forall], [exists] or [nabla]. *)
type binder = Forall | Exists | Nabla
(** Binary operator: [ = ], [ /\ ], [ \/ ] or [ => ] *)
type binop = Eq | And | Or | Arrow
type term

(** Reference on a term. Enables sharing. *)
type ptr

(** Substitution term. *)
type envitem = Dum of int | Binding of term * int

(** Substitution environment. *)
type env = envitem list

(** Term of type [term] observed via the function [observe].
  * Doesn't use the constructor [Ptr]. *)
type rawterm =
  | QString of string
  | Nat of int
  | Var of var
  | DB of int (** De Bruijn index of the variable (starting with 1) *)
  | NB of int (** local timestamp of the nabla variable *)
  | True
  | False
  | Binop of binop * term * term
  | Binder of binder * int * term (** n-ary quantification (the abstraction is implicit) *)
  | Lam of int * term (** n-ary abstraction *)
  | App of term * term list
  | Susp of term * int * int * env
  | Ptr of ptr

(** {6 Creating terms} *)

(** Access to a term. *)
val observe : term -> rawterm

(** Access to a non-variable term. *)
val deref : term -> term

val qstring : string -> term
val nat : int -> term
val db : int -> term
val nabla : int -> term
val op_true : term
val op_false : term
val op_binop : binop -> term -> term -> term
val op_eq : term -> term -> term
val op_and : term -> term -> term
val op_or : term -> term -> term
val op_arrow : term -> term -> term

(** [binder b n t] adds [n] times quantifier [b] around [t]. *)
val binder : binder -> int -> term -> term

(** [lambda n t] adds [n] abstractions around [t]. *)
val lambda : int -> term -> term

(** [app hd tl] applies [hd] to the list [tl],
  * and merges the lists of arguments if [hd] is a partial application. *)
val app : term -> term list -> term

val susp : term -> int -> int -> env -> term

(** {6 Term equalities} *)

exception NonNormalTerm

(** Fast observational equality; no normalization is peformed. *)
val eq : term -> term -> bool

(** Equivariant checking. *)
val eqvt : term -> term -> bool

(** {6 Creating and extracting variables} *)

(** An internal map is used to attach a naming hint for the pretty printer
  * to all variables, not only those built by the parser.
  * It is designed to not interfere with the GC. *)

(** Generate a fresh variable, attach a naming hint to it. *)
val fresh : ?name:string -> lts:int -> ts:int -> tag -> term

val get_var : term -> var

(** {6 Binding variables} *)

(** Binding a variable to a term in a destructive way,
  * saving and restoring previous states of the terms. *)

type state

val save_state : unit -> state
val restore_state : state -> unit

type subst
type unsubst

val bind : term -> term -> unit

val get_subst   : state -> subst
val apply_subst : subst -> unsubst
val undo_subst  : unsubst -> unit

(** Check if two substitutions are equal. *)
val eq_subst    : subst -> subst -> bool

(** {6 Handling variable names} *)

(** [namespace] is the type of a map used to obtain the exact same
  * variable term for representing all occurrences of that variable
  * -- used by the parser. *)
type namespace

val save_namespace : unit -> namespace
val restore_namespace : namespace -> unit

(** Get the unique variable attached to that name, preserving sharing.
  * If it does not exist, the variable is created with the provided [tag]
  * and both levels to 0.
  * If the [tag] is not provided, it is infered from the name. *)
(* XXX do we still infer the tag or not? *)
val atom : ?tag:tag -> string -> term

(** @return a generic name for the variable (neither unique nor real) *)
val get_var_name : var -> string

(** Find an unique name for [v] (based on a naming hint if there is one)
  * and registers it in the symbols table. *)
val get_name : term -> string

(** [get_dummy_name prefix] finds a free name starting with [prefix]
  * and registers it. If [start] is not provided,
  * the attempted suffixes will be "", "0", "1", etc.
  * If it is provided it will be used as the first suffix to try. *)
val get_dummy_name  : ?start:int -> string -> string

(** List of [n] new dummy names, most recent first. *)
val get_dummy_names : ?start:int -> int -> string -> string list

(** Check whether the name is attached to a variable in the namespace. *)
val is_free : string -> bool

(** Remove the name and its variable from the namespace. *)
val free    : string -> unit

(** {6 Copying} *)

(** @return an eigenvar copier.
  * Preserves sharing inside the set of copied terms.
  * When [passive] is passed to the copier,
  * it only propagates what's been copied when active,
  * but doesn't copy newly encountered variables.
  * Input terms should be normalized. *)
val copy_eigen : unit -> (?passive:bool -> term -> term)

(** Copy a term.
  * No sharing is maintained, except possibly on pointers to variables. *)
val simple_copy : term -> term

(** Copy a term maintaining shared structures. *)
val shared_copy : term -> term

(** {6 Abstracting} *)

(** [abstract var t] builds the abstraction of [t] over [var],
  * which may be either a variable or a nabla index.
  * This function is not destructive and hence breaks the sharing. *)
val abstract : term -> term -> term

(** [quantify b var t] builds the [b]-quantification of [t] over [var].
  * See [abstract]. *)
val quantify : binder -> term -> term -> term

(** [abstract_flex var t] is similar to abstract var t,
  * but will abstract flexible subterms headed by var. *)
val abstract_flex : term -> term -> term

(** {6 Extract variable terms} *)

(** [get_vars test ts] computes the list of variables [v] occuring in
  * the list of normalized terms [ts] and which satisfy [test v]. *)
val get_vars : (var -> bool) -> term list -> term list

(** [logic_vars ts] computes the list of logic variables [v] occuring in
  * the list of normalized terms [ts]. *)
val logic_vars : term list -> term list

(** [eigen_vars ts] computes the list of eigen variables [v] occuring in
  * the list of normalized terms [ts]. *)
val eigen_vars : term list -> term list

(** [get_nablas x] computes the list of nabla variables [n] occuring in
  * the normalized term [x]. *)
val get_nablas : term -> int list

(** {6 Convenience} *)

(** Infix (some of them) shortcuts. *)
module Notations :
  sig
    val ( %= ) : term -> term -> bool           (** Equality *)
    val ( !! ) : term -> rawterm                (** Observation *)
    val ( // ) : int -> term -> term            (** Abstraction *)
    val ( ^^ ) : term -> term list -> term      (** Application *)
  end

(** Generate a fresh (constant) variable.
  * @return its name *)
val fresh_name : string -> string

(** @return timestamp of the variable *)
val get_var_ts : var -> int

(** @return local timestamp of the variable *)
val get_var_lts : var -> int
