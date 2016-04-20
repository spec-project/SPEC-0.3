(****************************************************************************)
(* An implementation of Higher-Order Pattern Unification                    *)
(* Copyright (C) 2006-2011 Nadathur, Linnell, Baelde, Ziegler, Gacek, Heath *)
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

(** Terms pretty-printing. *)

(** Convert a term.
  * Ensures consistent namings, using naming hints when available.
  * Behaves consistently from one call to another
  * unless Term.reset_namespace is called between executions.
  *
  * The names from [generic] and [bound] are assumed not to conflict with
  * any other name. The good way to ensure that is to use
  * [Term.get_dummy_name] and [Term.free].
  *
  * The input term should be fully normalized.
  * @param generic list of names for generic variables
  * @param bound list of names for "free bound variables" *)
val term_to_string_full :
  generic:string list -> bound:string list -> Term.term -> string

(** Convert a term. Like [term_to_string_full], plus allows debugging. *)
val term_to_string_full_debug :
  generic:string list -> bound:string list -> bool -> Term.term -> string

(** Convert a term. Like [term_to_string_full], plus does full normalization
  * and generic names generation. *)
val term_to_string : ?bound:string list -> Term.term -> string

(** For use with [Format.printf]. Like [term_to_string]. *)
val pp_term : Format.formatter -> Term.term -> unit

(** Output to stdout. Like [term_to_string]. *)
val print_term : ?bound:string list -> Term.term -> unit

(** Utility for tools such as Taci which push down formula-level abstraction
  * to term level abstractions. Dummy names should be created (and freed)
  * during the printing of the formula, and passed as the bound names to this
  * function, which won't display the lambda prefix.
  * The input term should have at least [List.length bound] abstractions
  * at toplevel. *)
val pp_preabstracted :
  generic:string list -> bound:string list ->
  Format.formatter -> Term.term -> unit

val term_to_string_preabstracted :
  generic:string list -> bound:string list -> Term.term -> string
