(**************************************************************************)
(*  This program is free software; you can redistribute it and/or modify  *)
(*  it under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation; version 2 of the License.               *)
(*                                                                        *)
(*  This program is distributed in the hope that it will be useful, but   *)
(*  WITHOUT ANY WARRANTY; without even the implied warranty of            *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU     *)
(*  General Public License for more details.                              *)
(*                                                                        *)
(*  You should have received a copy of the GNU General Public License     *)
(*  along with this program; if not, write to the Free Software           *)
(*  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA         *)
(*  02110-1301 USA                                                        *)
(*                                                                        *)
(**************************************************************************)

(*  Adapted from:                                                         *)
(*  Mini, a type inference engine based on constraint solving.            *)
(*  Copyright (C) 2006. François Pottier, Yann Régis-Gianas               *)
(*  and Didier Rémy.                                                      *)

(** This module provides a constraint solver based on unification
    under a mixed prefix. *)

(** The solver environment. *)
type environment

(** The constraint to solve. *)
type tconstraint = TypeConstraint.tconstraint

(** A [solving_step] describes a elementary step of the solver. *)
type solving_step =
  | Init of tconstraint
  | Solve of tconstraint
  | Solved of tconstraint
  | UnifyTerms of TypeConstraint.crterm * TypeConstraint.crterm
  | UnifyVars of TypeConstraint.variable * TypeConstraint.variable
  | Generalize of int
                  * TypeConstraint.variable list (* rigid variables *)
                  * TypeConstraint.variable list (* flexible variables *)

(** [solve tracer c] solves [c] by doing in-place modifications resulting
    in an environment. *)
val solve: ?tracer:(solving_step -> unit)
  -> tconstraint -> environment

(** a simple tracer *)
val tracer: unit -> solving_step -> unit

(** [environment_as_list env] converts [env] into a list. *)
val environment_as_list : environment -> (string * TypeConstraint.variable) list

(** [print_env printer env] use the variable printer [printer] in
    order to display [env]. *)
val print_env: (TypeConstraint.variable -> string) -> environment -> unit

type solver_error =
  (** [TypingError] is raised when an inconsistency is detected during
      constraint solving. *)
  | TypingError of Location.t

  (** [UnboundIdentifier] is raised when an identifier is undefined in
      a particular context. *)
  | UnboundIdentifier of Location.t * string

  (** [CannotGeneralize] when the type of an expression cannot be
      generalized contrary to what is specified by the programmers
      using type annotations. *)
  | CannotGeneralize of Location.t * TypeConstraint.variable

  (** [NonDistinctVariables] is raised when two rigid type variables have
      been unified. *)
  | NonDistinctVariables of Location.t * (TypeConstraint.variable list)

exception Error of solver_error

val error_msg: solver_error -> string
