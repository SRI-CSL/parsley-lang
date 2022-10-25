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

open Parsing
open Ast
open TypingEnvironment

module StringSet : Set.S with type elt = string

(* pattern matrix utilities *)

val default_mat:
  (('a, 'b, mod_qual) pattern list * 'c) list -> (('a, 'b, mod_qual) pattern list * 'c) list

val specialize_mat:
  environment
  -> (('a, 'b, mod_qual) pattern list * 'c) list
  -> ('d, 'e, mod_qual) pattern
  -> (('a, 'b, mod_qual) pattern list * 'c) list

val is_complete_sig:
  environment -> ('a, 'b, mod_qual) pattern list -> bool

val first_col:
  ('a list * 'b) list -> 'a list

val nth_col:
  ('a list * 'b) list -> int -> 'a list

val swap_cols:
  ('a list * 'b) list -> int -> int -> ('a list * 'b) list

val roots:
  environment -> ('a, 'b, mod_qual) pattern list -> (('a, 'b, mod_qual) pattern * int) list

val unused_constructors:
  environment -> Ast.mname -> Ast.ident -> Ast.ident list -> StringSet.t

(* bitvector utilities *)

val bv_to_int: bool list -> int64
val int_to_bv: int64 -> int -> bool list

(* miscellaneous *)

val repeat: 'a -> int -> 'a list

module BVSet : sig
  include module type of Set.Make(Int64)
end
