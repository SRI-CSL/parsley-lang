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

(** This module provides the type algebra for the Parsley language. *)

(** The type algebra augments the {!CoreAlgebra} to relate it with
    the Parsley source language. *)

(** A type constructor is a type variable with higher-order kind.
    It is introduced as any type variable in the multi-equation set
    during the constraint generation. Then, an environment is given to
    the algebra in order to retrieve the type variable associated
    to the string representation of the type constructor. *)
type 'a environment = Ast.tname -> 'a CoreAlgebra.arterm

(** [tuple env ts] returns [t0 * ... * tn]. *)
val tuple : 'a environment -> 'a CoreAlgebra.arterm list -> 'a CoreAlgebra.arterm

(** [arrow env t1 t2] return the type [t1 -> t2]. *)
val arrow : 'a environment -> 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm

(** [arrow env ts] returns the type [t0 -> ... -> tn]. *)
val n_arrows: 'a environment -> 'a CoreAlgebra.arterm list -> 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm

(** [result_type env t] returns the result type of the type [t] if
    [t] is an arrow type. *)
val result_type :  'a environment -> 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm

(** [arg_types env t] returns the argument types of the type [t] if
    [t] is an arrow type. *)
val arg_types : 'a environment -> 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm list

val tycon_args : 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm list
val tycon_name : 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm

(** [type_of_primitive p] returns the type of a source language primitive. *)
val type_of_primitive : 'a environment -> Ast.primitive_literal -> 'a CoreAlgebra.arterm

(** The type of predefined data constructors. *)
type builtin_dataconstructor = Ast.dname * Ast.tname list * Ast.type_expr

(** [init_builtin_env variable_maker] uses [variable_maker] to build
    a typing environment that maps type constructor names to their arities,
    their type variables, and their data constructors. *)
val init_builtin_env: (?name:Ast.tname -> unit -> 'a)
  -> (Ast.tname * (Ast.kind * 'a CoreAlgebra.arterm * builtin_dataconstructor list)) list

(** [builtin_env] has entries for each type constructor name that
   specify its kind and data constructors. *)
val builtin_env:
  (Ast.tname
   * (Ast.kind * (Ast.dname * Ast.tname list * Ast.type_expr) list))
  array
