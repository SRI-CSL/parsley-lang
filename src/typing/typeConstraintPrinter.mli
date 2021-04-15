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

(** The constraint over equality between terms. *)
type formula =
  (MultiEquation.crterm, MultiEquation.variable) TypeConstraint.type_constraint

(** Pretty printer for [formula]. *)
val printf_constraint: PrettyPrinter.mode -> formula -> unit

(** Pretty printer for [width_constraint]. *)
val print_width_predicate:  TypeConstraint.width_predicate -> string
val print_width_constraint: TypeConstraint.width_constraint -> unit

(* helper printers *)
val print_crterm: MultiEquation.crterm -> string
val print_variable: MultiEquation.variable -> string

(* printer mode activator *)
val active_mode: PrettyPrinter.mode -> unit
