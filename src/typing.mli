(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2012 Quentin Heath                                         *)
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

(** Kinds, types, checking and pretty-printing. *)

(** Input signature of the functor {!Typing.Make}. *)
module type INPUT = sig
  (** Type of some additional information. *)
  type pos

  (** Dummy information. *)
  val dummy_pos : pos
end

(** Output signature of the functor {!Typing.Make}. *)
module type S = sig
  type pos
  val dummy_pos : pos

  (** {6 Kinds} *)

  (** Kind allowing type operators. *)
  type ki
  val ki_arrow : ki list -> ki -> ki
  val ktype : ki

  (** Print a kind. *)
  val pp_kind : Format.formatter -> ki -> unit
  val kind_to_string : ki ->string

  (** {6 Types} *)

  (** Simple types (including some predefined ones). *)
  type ty
  (** Type composition. *)
  val ty_arrow : ty list -> ty -> ty
  (** User-defined base type. *)
  val tconst : string -> ty
  val tfunc : string -> ty list -> ty
  val tprop : ty
  val tstring : ty
  val tnat : ty
  (** Type variables (for polymorphism). *)
  val tvar : int -> ty
  (** Type parameters (for type inference). *)
  val tparam : int -> ty
  val fresh_tyvar : unit -> ty
  val fresh_typaram : unit -> ty
  val get_typaram : string -> ty
  val build_abstraction_types : int -> ty list * ty

  (** Print a type. *)
  val pp_type : Format.formatter -> ty -> unit
  val type_to_string : ty -> string

  (** {6 Kind checking} *)

  (** Kind checking error. *)
  exception Type_kinding_error of pos * ki * ki

  (** [kind_check ty expected_kind] checks that type [ty]
    * and all its subtypes are of the kind [expected_kind] (usually [TKind]).
    * In the current implementation, types are simple types,
    * so it always succeeds (except when given a non-existing type).
    *
    * @param atomic_kind function returning the kind of an atomic type
    * @return [(flex,hollow,propositional,higher_order)]
    * (describing whether the type is an unresolved type parameter,
    * contains unresolved type parameters, ends with [TProp]
    * or contains [TProp]) *)
  val kind_check :
    ?atomic_kind:(pos * string -> ki) ->
    ty ->
    ki ->
    bool * bool * bool * bool

  (** {6 Type unifying} *)

  (** Type unifier type.
    * Used as an environment for the type variables
    * (a binding [k,v] symbolizes the substitution [(TVar k) -> v]). *)
  type type_unifier

  (** Apply a function on each substitution of a unifier. *)
  val iter : (int -> ty -> unit) -> type_unifier -> unit

  val global_unifier : type_unifier ref

  (** Clear the global unifier. *)
  val clear : unit -> unit

  (** Display a type in its {i ground form}, ie a unique form with regards to the
    * unifier. *)
  val ty_norm : ?unifier:type_unifier -> ty -> ty

  (** Print a type in a more unique way. *)
  val pp_type_norm :
    ?unifier:type_unifier -> Format.formatter -> ty -> unit
  val type_to_string_norm :
    ?unifier:type_unifier -> ty -> string

  (** Type incompletely inferred. *)
  exception Hollow_type of string

  (** Check whether a type was completely inferred. *)
  val check_ground : string -> ty -> unit

  (** Type unification impossible. *)
  exception Type_unification_error of ty * ty * type_unifier

  (** Refines the provided unifier accordingly to a pair of types.
    * TODO Does this unification procedure have a name?*)
  val unify_constraint : type_unifier -> ty -> ty -> type_unifier
  val fresh_inst : ty -> ty
end

(** Functor building an implementation of the typing structure
  * given a position type. *)
module Make (I : INPUT) : S with type pos = I.pos
