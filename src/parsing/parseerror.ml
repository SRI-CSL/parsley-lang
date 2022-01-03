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
  | Nonpositive_bitvector_width of int
  | Missing_bitvector_width
  | Invalid_bitvector_syntax

exception Error of parse_error * Location.t

let msg = Location.msg

let error_msg l = function
  | Invalid_integer s ->
      msg "%s:\n Invalid integer: `%s'." l s
  | Undeclared_format_param s ->
      msg "%s:\n Undeclared format param `%s'." l s
  | Untyped_format_param s ->
      msg "%s:\n No type declared for format param `%s'." l s
  | Invalid_bitvector_constructor s ->
      msg "%s:\n Constructor `%s' cannot use bitvector syntax." l s
  | Invalid_bitvector_nonterminal s ->
      msg "%s:\n Non-terminal `%s' cannot use bitvector syntax." l s
  | Nonpositive_bitvector_width w ->
      msg "%s:\n Illegal non-positive width %d for bitvector." l w
  | Missing_bitvector_width ->
      msg "%s:\n BitVector requires an explicit bit-width." l
  | Invalid_bitvector_syntax ->
      msg "%s:\n Incorrect syntax for BitVector use." l
