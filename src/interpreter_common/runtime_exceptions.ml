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

type error =
  | Division_by_zero
  | Length_mismatch of string * int * int
  | Index_bound of int * int
  | Unsafe_operation_failure of string
  | Invalid_argument of string * string
  | Overflow of string
  | View_bound of string * string
  | No_foreign_impl_decl of string * string * int
  | No_foreign_impl_found of string * string * int
  | Unsupported_foreign_nargs of string * string * int
  | Buffer_creation_failure of string
  | Refill_not_on_root_view of int
  | Refill_no_handler
  | Refill_failed of int (* needed *) * int (* filled *)

exception Runtime_exception of Location.t * error

let fault l e =
  raise (Runtime_exception (l, e))

let error_msg = function
  | Division_by_zero ->
      "Division by zero."
  | Length_mismatch (op, ll, lr) ->
      Printf.sprintf "Mismatched lengths for '%s': %d vs %d."
        op ll lr
  | Index_bound (idx, len) ->
      Printf.sprintf "Index %d is out of bounds for list of length %d."
        idx len
  | Unsafe_operation_failure op ->
      Printf.sprintf "Unsafe operation '%s' failed." op
  | Invalid_argument (op, s) ->
      Printf.sprintf "Invalid argument to '%s': %s" op s
  | Overflow op ->
      Printf.sprintf "Operation '%s' overflowed." op
  | View_bound (op, m) ->
      Printf.sprintf "View operation '%s' went out of bounds: %s." op m
  | No_foreign_impl_decl (m, f, n) ->
      Printf.sprintf "No OCaml implementation declared for foreign function %s.%s (taking %d arguments)."
        m f n
  | No_foreign_impl_found (m, f, n) ->
      Printf.sprintf "No OCaml implementation found for foreign function %s.%s (taking %d arguments)."
        m f n
  | Unsupported_foreign_nargs (m, f, n) ->
      Printf.sprintf "%d arguments not supported for foreign function %s.%s."
        n m f
  | Buffer_creation_failure nm ->
      Printf.sprintf "Unable to create parse buffer for `%s'." nm
  | Refill_not_on_root_view i ->
      Printf.sprintf "The `require_remaining` assertion (for %d bytes) requires a root view."
        i
  | Refill_no_handler ->
      Printf.sprintf "Parse buffer needs refill, but no refill handler was specified."
  | Refill_failed (need, got) ->
      Printf.sprintf "Refill of parse buffer failed: %d bytes needed, %d refilled."
        need got
