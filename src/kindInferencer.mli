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

(** This module provides a simple inference engine for the kinds
    of the Parsley type system. *)

(** Internal kind representation. *)
type t

(** The kind inference engine uses an environment implemented by
    two functions (get, add). *)
type env = (Ast.tname -> Location.t -> t) * (Ast.tname -> t -> unit)

(** [fresh_kind] returns a fresh kind for a type. *)
val fresh_kind: unit -> t

(** [infer env typ] infers a kind for [typ]. *)
val infer: env -> Ast.type_expr -> t

(** [intern_kind env kind] internalizes a kind in the user-syntax. *)
val intern_kind: env -> Ast.kind -> t

(** [check env typ kind ] verifies that [typ] can be given the kind
    [kind]. *)
val check: env -> Ast.type_expr -> t -> unit

(** [star] is the kind of ml values. *)
val star : t
