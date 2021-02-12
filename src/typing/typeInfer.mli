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

(** This module converts the problem of type inference into the
    problem of constraint solving by a transformation of the typing
    relationships in the program into typing constraints. *)

open Parsing

 (** Constraint contexts. *)
type context = TypeConstraint.tconstraint -> TypeConstraint.tconstraint

(** [generate_constraint p] generates a closed constraint that describes
    the typing of [p] and an annotated version of [p]. *)
val generate_constraint:
  (unit, unit) Ast.program ->
  TypeConstraint.tconstraint * TypingEnvironment.environment * (MultiEquation.crterm, int) Ast.program

(** Variable binding map *)

(* binding identifier *)
type varid = private int

module VEnv : sig
  type t
  val empty: t
  val add: t -> unit Ast.var -> varid Ast.var * t
  val extend: t -> string -> varid Ast.var -> t
  val lookup: t -> unit Ast.var -> varid Ast.var option
end

(** [infer_spec s] generates a constraint context that describes
    spec [s] and an annotated version of [s]. *)
val infer_spec: TypingEnvironment.environment -> VEnv.t -> (unit, unit) Ast.program ->
  TypingEnvironment.environment * context * (MultiEquation.crterm, varid) Ast.program
