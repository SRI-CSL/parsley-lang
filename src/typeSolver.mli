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

include ConstraintSolver.SolverException

(** The solver environment. *)
type environment

(** The constraint to solve. *)
type tconstraint = (MultiEquation.crterm, MultiEquation.variable) TypeConstraint.type_constraint

(** A [solving_step] describes a elementary step of the solver. *)
type solving_step =
  | Init of tconstraint
  | Solve of tconstraint
  | Solved of tconstraint
  | UnifyTerms of MultiEquation.crterm * MultiEquation.crterm
  | UnifyVars of MultiEquation.variable * MultiEquation.variable
  | Generalize of int * MultiEquation.variable list

(** [solve tracer c] solves [c] by doing in-place modifications resulting
    in a environment. *)
val solve: ?tracer:(solving_step -> unit)
  -> tconstraint -> environment

(** [environment_as_list env] converts [env] into a list. *)
val environment_as_list : environment -> (string * MultiEquation.variable) list

(** [print_env printer env] use the [printer] of variable in order to
    display [env]. *)
val print_env :
  ?use_user_def:'a -> (TypeConstraint.variable -> string) -> environment -> unit

