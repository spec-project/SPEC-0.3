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

(** System variables, predefined predicates,
  * definitions bulding and handling. *)

(** Predefined and internal predicates. *)
module Logic :
  sig
    (** {6 Non-logical extensions ({e EXPERIMENTAL})} *)

    (** {[_not : prop -> prop]} Standard negation-as-failure, as in prolog. *)
    val var_not : Term.var

    (** {[_if : prop -> prop -> prop -> prop]} If-Then-Else:
      * [_if P Q R] is basically equivalent to [(P /\ Q) \/ (not(P) /\ R)].
      * The slight difference is that the second disjunct
      * will not be tried if P is successful. *)
    val var_ite : Term.var

    (** {[_abstract : 'a -> (('b -> 'a) -> 'a) -> 'a -> prop]}
      * [_abstract T Abs T'] assumes the logic variables in T are of type 'b,
      * abstracts them, applies the constructor Abs to each abstraction,
      * and unifies the result with T'.
      *
      * Example query:
      * {v ?= _abstract (pr X Y) abs T.
Solution found:
 X = X
 Y = Y
 T = (abs (x1\ abs (x2\ pr x1 x2)))
More [y] ? y
No more solutions. v}
      *
      * {e WARNING}: Because [_abstract] can abstract any logic variables,
      * and because while the input files are type-checked,
      * the underlying abstract machine of bedwyr is untyped,
      * the abstraction produced by [_abstract] may not always respect
      * the type of the constructor Lam.
      *
      * For example, consider the above example.
      * If [pr] is of type [alpha -> beta -> gamma],
      * for some distinct types [alpha] and [beta],
      * then the above query will still succeed despite the fact that
      * [abs] is applied to terms of types [alpha -> gamma]
      * and [beta -> gamma]:
      * {v ?= #typeof pr.
pr : alpha -> beta -> gamma
?= #typeof abs.
abs : (beta -> gamma) -> gamma
?= #typeof _abstract.
_abstract : ?4 -> ((?5 -> ?4) -> ?4) -> ?4 -> prop
?= #typeof abs (x1\ abs (x2\ pr x1 x2)).
At line 4, characters 30-31:
Typing error: this expression has type beta but is used as
alpha. v}
      *
      * Hence type checking does not guarantee runtime type soundness
      * ("well typed programs don't go wrong").
      * A solution to this would be to make the bedwyr engine aware
      * of the type constraints,
      * so that it only abstracts variables of the correct types. *)
    val var_abspred : Term.var

    (** {[_distinct : prop -> prop]} Calling [_distinct P]
      * directs bedwyr to produce only distinct answer substitutions:
      * {v ?= true \/ true.
Yes.
More [y] ?
Yes.
More [y] ?
No more solutions.
?= _distinct (true \/ true).
Yes.
More [y] ?
No more solutions.
?= v} *)
    val var_distinct : Term.var

    (** {[_rigid : 'a -> prop]} This is a meta-level assertion predicate.
      * [_rigid X] will throw an assertion
      * (hence causes the prover to abort) if [X] is not a ground term. *)
    val var_assert_rigid : Term.var

    (** {[_abort : prop]} This predicate aborts the proof search
      * and returns to the toplevel query (if in interactive mode). *)
    val var_abort_search : Term.var

    (** {[_cut : prop -> prop]} Applying the predicate [_cut]
      * to a query removes the backtracking for that query.
      * That is, a query such as [cut P] will produce the first solution
      * (if any) to [P], and terminates. *)
    val var_cutpred : Term.var

    (** {[_eqvt : 'a -> 'a -> prop]}
      * This predicate checks that its arguments are
      * syntatically equivalent modulo renaming of nabla variables.
      *
      * For example:
      * {v ?= forall f, nabla x y, _eqvt (f x y) (f y x).
Yes.
More [y] ? y
No more solutions.
?= forall f, nabla x y, _eqvt (f x x) (f y y).
Yes.
More [y] ? y
No more solutions.
?= forall f, nabla x y, _eqvt (f x x) (f x y).
No. v} *)
    val var_check_eqvt : Term.var

    (** {6 I/O extensions} *)

    (** {[print : 'a -> prop]} Print a term and returns [true]. *)
    val var_print : Term.var

    (** {[println : 'a -> prop]} [print] +  '\n'. *)
    val var_println : Term.var

    (** {[printstr : 'a -> prop]} Print a string without quotation marks. *)
    val var_printstr : Term.var

    (** {[fprint : string -> 'a -> prop]} Print a term in the file
      * specified in the first argument and returns [true].
      * Fails if the file was not opened yet. *)
    val var_fprint : Term.var

    (** {[fprintln : string -> 'a -> prop]} [println] in a file. *)
    val var_fprintln : Term.var

    (** {[var_fprintstr : string -> 'a -> prop]} [printstr] in a file. *)
    val var_fprintstr : Term.var

    (** {[fopen_out : string -> prop]} Open a file for writing. *)
    val var_fopen_out : Term.var

    (** {[fclose_out : string -> prop]} Close an open file. *)
    val var_fclose_out : Term.var

    (** Example:
      * {v ?= fopen_out "test.txt".
Yes.
More [y] ? y
No more solutions.
?= fprint "test.txt" "Test printing".
Yes.
More [y] ? y
No more solutions.
?= fclose_out "test.txt".
Yes.
More [y] ? y
No more solutions. v}
      * The file "test.txt" will contain the string "Test printing". *)
  end

(** Simple debug flag, can be set dynamically from the logic program. *)
val debug : bool ref

(** Enables the display of computation times. *)
val time : bool ref

val close_all_files : unit -> unit
val close_user_file : string -> unit
val get_user_file : string -> out_channel
val open_user_file : string -> out_channel

open Input

(** {6 Type declarations} *)

exception Invalid_type_declaration of string * Input.pos *
            Typing.ki * string
val declare_type : Input.pos * string -> Typing.ki -> unit

(** {6 Constants and predicates declarations} *)

(** Describe whether tabling is possible, and if so, how it is used. *)
type flavour =
    Normal (** only unfolding can be done *)
  | Inductive (** tabling is possible, and loop is a failure *)
  | CoInductive (** tabling is possible, and loop is a success *)

exception Missing_type of string * Input.pos
exception Invalid_const_declaration of string * Input.pos *
            Typing.ty * string
exception Invalid_flavour of string * Input.pos *
            flavour * flavour
exception Invalid_pred_declaration of string * Input.pos *
            Typing.ty * string
exception Invalid_bound_declaration of string * Input.pos *
            Typing.ty * string

val string_of_flavour : flavour -> string

val declare_const : Input.pos * string -> Typing.ty -> unit

(** Declare predicates.
  * @return the list of variables and types
  *  corresponding to those predicates *)
val declare_preds :
  (Input.flavour * Input.pos * string * Typing.ty) list ->
  (Term.var * Typing.ty) list

(** {6 Typechecking, predicates definitions} *)

exception Missing_declaration of string * Input.pos option
exception Inconsistent_definition of string * Input.pos * string

(** Translate a pre-term, with typing and position information,
  * into a term, with variable sharing.
  * Type checking (or rather type inference) is done on the fly,
  * and no type information is kept in the terms from this point.
  * If the term isn't well typed, or has a type that isn't [prop],
  * an exception is raised and the global type unifier isn't updated. *)
val translate_query : Input.preterm -> Term.term

(** For each [(p,h,b)] of [c],
  * [add_clauses l c] adds the clause [h := b] to a definition,
  * as long as the var of the corresponding predicate is in the list [l]. *)
val add_clauses :
  (Term.var * Typing.ty) list ->
  (Input.pos * Input.preterm * Input.preterm) list ->
  unit

(** {6 Theorem definitions} *)

exception Inconsistent_theorem of string * Input.pos * string

(** If possible, add the theorem to the tabling extended rules. *)
val add_theorem : (Input.pos * string * Input.preterm) -> unit

(** {6 Using predicates} *)

exception Missing_definition of string * Input.pos option
exception Missing_table of string * Input.pos option

(** Remove all definitions. *)
val reset_decls : unit -> unit

(** Get a definition.
  * @param check_arity the expected arity of the predicate
  * @raise Missing_declaration if [head_tm] is not an existing predicate
  *)
val get_def :
  check_arity:int ->
  Term.term -> flavour * Term.term * Term.term * Table.t option * Typing.ty

(** Update a definition *)
val update_def : Term.term -> Term.term -> unit 

(** Remove a definition. *)
val remove_def : Term.term -> unit

(** Remove all tables. *)
val clear_tables : unit -> unit

(** Remove a table. *)
val clear_table : Input.pos * Term.term -> unit

(** {6 I/O} *)

(** Display the inferred type of every declared object. *)
val print_env : unit -> unit

(** Perform type checking on a pre-term and display the inferred type.
  * The goal of this is to use the REPL to check the validity of a term
  * without messing with the future inference,
  * so the global type unifier is left unchanged
  * even if the term is well typed and of type [prop]. *)
val print_type_of : Input.preterm -> unit

(** Display the content of a table. *)
val show_table : Input.pos * Term.term -> unit

(** Save the content of a table to a file.
  * The proved and disproved entries are stored as arguments
  * to the predicates [proved] and [disproved], respectively. *)
val save_table : Input.pos * Term.term -> string -> unit

(** {6 Misc} *)

exception Interrupt

(** @return [true] if a user interruption was detected since the last call to
  * [check_interrupt], [false] otherwise. *)
val check_interrupt : unit -> bool
