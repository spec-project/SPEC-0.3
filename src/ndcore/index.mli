(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006-2011 David Baelde, Alwen Tiu                          *)
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

(** Implementation of an index structure used for tabling.
  *
  * An index represents a set of terms, in which eigenvariables may be allowed
  * but not logic variable -- since this requires suspensions.
  * The terms are abstracted over their eigenvars in the set.
  * For efficiency, the index lookup first parses the "rigid" structure of a
  * term in linear time, and extracts variables, and then takes care of the
  * equalities among these variables.
  *
  * Currently the Nabla indices are handled as part of the rigid structure of
  * terms, which means that weakening and swapping are not supported.
  * Later, the set of nabla variables could be extracted and simplified to an
  * essential representation just like eigenvariables. *)


(** Option to turn on/off equivariant indexing. *)
val eqvt_index : bool ref

(** {6 Indexing} *)

(** Type of an index of elements of type ['a]. *)
type 'a t
val empty  : 'a t

(** Eigen variable in level 0, or logic variable. *)
exception Cannot_table

(** {6 Access} *)

(** Take an index and some arguments,
  * and returns [update], [found] and [remove]. *)
val access :
  allow_universal:bool ->
  allow_existential:bool ->
  switch_vars:bool ->
  'a t -> Term.term list ->
  ('a -> 'a t) * 'a option * (unit -> 'a t)

(** {6 Fold} *)

(** Apply a function on each binding of index. *)
val iter   : 'a t -> (Term.term -> 'a -> unit) -> unit
