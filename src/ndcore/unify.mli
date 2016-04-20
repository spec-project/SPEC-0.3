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

(** Higher Order Pattern Unification *)

type error =
  | OccursCheck
  | TypesMismatch
  | ConstClash of (Term.term * Term.term)

(** Miscellaneous unification errors. *)
exception Error      of error

(** Not a pattern. *)
exception NotLLambda of Term.term

(** Formula encountered by the unifier. *)
exception Formula_as_Term of Term.term

module type Param =
sig
  val instantiatable : Term.tag
  val constant_like  : Term.tag
end

module Make : functor (P:Param) -> sig
  (** Either succeeds and realizes the unification substitutions as side
    * effects, or raises an exception to indicate nonunifiability
    * or to signal a case outside of the LLambda subset.
    *
    * When an exception is raised, it is necessary to catch this
    * and at least undo bindings for variables made in the attempt to unify.
    * This has not been included in the code at present.
    *
    * This procedure assumes that there are no iterated lambdas
    * or applications at the top level of the two terms it gets.
    * Any necessary adjustment of binders through the eta rule
    * is done on the fly. *)
  val pattern_unify : Term.term -> Term.term -> unit
end
