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

(** [variables_of_typ ty] returns the type variables of [ty]. *)
val variables_of_typ : Ast.type_expr -> Location.t Misc.StringMap.t

(** [arrow env x1 x2] builds the internal representation of the
    type [x1 -> x2]. *)
val arrow :
  TypingEnvironment.environment -> MultiEquation.crterm -> MultiEquation.crterm -> MultiEquation.crterm

(** [arity (t1 -> ... -> tn)] returns [n]. *)
val arity : Ast.type_expr -> int

(** [tycon t xs] builds the internal representation of the type [t xs]. *)
val tycon : TypingEnvironment.environment -> Ast.ident -> MultiEquation.crterm list -> MultiEquation.crterm

(** [intern env ty] converts [ty] into its internal representation. *)
val intern : TypingEnvironment.environment -> Ast.type_expr -> MultiEquation.crterm

(** [internal_let_env env fqs rqs] internalizes the flexible variables
    [fqs] and the rigid variables [rqs] into [env]. *)
val intern_let_env : Location.t -> TypingEnvironment.environment -> Ast.ident list -> Ast.ident list ->
  MultiEquation.variable list * MultiEquation.variable list * TypingEnvironment.environment

(** [intern_scheme env x fqs ty] returns the internal representation
    of the type scheme [forall fqs.ty] and the binding of [x] to it. *)
val intern_scheme : Location.t -> TypingEnvironment.environment -> string -> Ast.ident list ->
  Ast.type_expr -> (MultiEquation.crterm, MultiEquation.variable) TypeConstraint.scheme

(** [canonicalize_dcon typ constr] returns the canonical name for the
    data constructor [constr] of type [typ]. *)
val canonicalize_dcon : string -> string -> string
