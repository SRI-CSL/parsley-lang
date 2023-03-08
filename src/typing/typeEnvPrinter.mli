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

(** This module provides a simple pretty-printer for the terms
    maintained by a unifier. *)

(** printing syntax for a type or type operator *)

open Parsing

type print_info =
  MultiEquation.variable     (* type or type operator *)
  * Ast.full_tname           (* name *)
  * arg list                 (* syntax for type arguments *)
  * bool                     (* whether type operator is infix *)
  * TypeAlgebra.associativity
  * bool                     (* parentheses for disambiguation *)

and arg =
  Arg of print_info

type type_info =
    (MultiEquation.variable * string) list (* forall quantifiers *)
  * print_info

(** type information.  See below for the `bool` argument. *)
val variable_type_info: bool -> MultiEquation.variable -> type_info
val term_type_info:     bool -> MultiEquation.crterm   -> type_info

(** [print_* is_type_scheme x] returns a printable
    representation of the object [x]. Consecutive calls to [print_*]
    share the same variable naming conventions, unless [reset] is
    called in between. *)
val print_variable: bool -> MultiEquation.variable -> string
val print_term:     bool -> MultiEquation.crterm   -> string

(** [reset ()] clears the memoization table used to compute the above info. *)
val reset: unit -> unit
