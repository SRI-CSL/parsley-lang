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

type parse_error =
  | Invalid_integer of string
  | Invalid_integer_literal of int * Ast.num_t
  | Undeclared_format_param of string
  | Untyped_format_param of string
  | Invalid_bitvector_constructor of string
  | Invalid_bitvector_nonterminal of string
  | Nonpositive_bitvector_width of int
  | Missing_bitvector_width
  | Invalid_bitvector_syntax
  | InvalidBinding of Ast.literal

exception Error of parse_error * Location.t

let error_msg = function
  | Invalid_integer s ->
      Printf.sprintf "Invalid integer: `%s'." s
  | Invalid_integer_literal (i, n) ->
      Printf.sprintf "Invalid integer literal for %s: `%d'."
        (Ast.str_of_num_t n) i
  | Undeclared_format_param s ->
      Printf.sprintf "Undeclared format param `%s'." s
  | Untyped_format_param s ->
      Printf.sprintf "No type declared for format param `%s'." s
  | Invalid_bitvector_constructor s ->
      Printf.sprintf "Constructor `%s' cannot use bitvector syntax." s
  | Invalid_bitvector_nonterminal s ->
      Printf.sprintf "Non-terminal `%s' cannot use bitvector syntax." s
  | Nonpositive_bitvector_width w ->
      Printf.sprintf "Illegal non-positive width %d for bitvector." w
  | Missing_bitvector_width ->
      Printf.sprintf "BitVector requires an explicit bit-width."
  | Invalid_bitvector_syntax ->
      Printf.sprintf "Incorrect syntax for BitVector use."
  | InvalidBinding b ->
      Printf.sprintf "`%s' cannot be parsed as a valid binding identifier."
        (Location.value b)
