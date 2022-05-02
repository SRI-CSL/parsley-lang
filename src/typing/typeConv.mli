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

(** This module transforms types from the user's syntax to the
    internal representation of the inference engine. *)

open Parsing

(** [variables_of_typ ty] returns the type variables of [ty]. *)
val variables_of_typ: Ast.type_expr -> Location.t Misc.StringMap.t

(** [arrow env x1 x2] builds the internal representation of the
    type [x1 -> x2]. *)
val arrow :
  TypingEnvironment.environment -> MultiEquation.crterm -> MultiEquation.crterm -> MultiEquation.crterm

(** [bitvector_n env n] builds the internal representation of the
    type [bitvector n] for a concrete integer width [n]. *)
val bitvector_n:
  TypingEnvironment.environment -> int -> MultiEquation.crterm

(** [bitvector_t env n] builds the internal representation of the
    type [bitvector t] for a type [t]. *)
val bitvector_t:
  TypingEnvironment.environment -> MultiEquation.crterm -> MultiEquation.crterm

(** [arity (t1 -> ... -> tn)] returns [n]. *)
val arity : Ast.type_expr -> int

(** [intern env ty] converts [ty] into its internal representation. *)
val intern : TypingEnvironment.environment -> Ast.type_expr -> MultiEquation.crterm
