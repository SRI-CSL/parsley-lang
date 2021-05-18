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
  | Undeclared_format_param of string
  | Untyped_format_param of string
  | Invalid_bitvector_constructor of string
  | Invalid_bitvector_nonterminal of string
  | Negative_bitvector_width of int
  | Missing_bitvector_width
  | Invalid_bitvector_syntax

exception Error of parse_error * Location.t

let error_string = function
  | Invalid_integer s ->
      Printf.sprintf "invalid integer: '%s'" s
  | Undeclared_format_param s ->
      Printf.sprintf "undeclared format param '%s'" s
  | Untyped_format_param s ->
      Printf.sprintf "no type declared for format param '%s'" s
  | Invalid_bitvector_constructor s ->
      Printf.sprintf "constructor '%s' cannot use bitvector syntax" s
  | Invalid_bitvector_nonterminal s ->
      Printf.sprintf "non-terminal '%s' cannot use bitvector syntax" s
  | Negative_bitvector_width w ->
      Printf.sprintf "illegal negative width %d for bitvector" w
  | Missing_bitvector_width ->
      Printf.sprintf "BitVector requires an explicit bit-width"
  | Invalid_bitvector_syntax ->
      Printf.sprintf "Incorrect syntax for BitVector use"
