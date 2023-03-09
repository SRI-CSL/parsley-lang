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
open Values

(* These errors indicate internal bugs. *)
type error =
  | Type_error of string * int * vtype * vtype
  | Bitrange_index of int * int
  | Bitrange_range of int (* hi *) * int (* lo *)
  | No_field of string
  | Bitfield_length_mismatch of string * string * int * int
  | Unknown_stdlib of string * string * int
  | Unknown_std_nonterm of string * int
  | Bad_subterm_path of Anf_common.occurrence * Anf_common.occurrence
  | Bad_subterm_index of constr * int * Anf_common.occurrence
  | Unknown_attribute of string * string
  | Invalid_constructor_value of constr * int

let error_msg =
  let pr_occ = Anf_common.string_of_occurrence in
  function
  | Type_error (op, arg, r, e) ->
      Printf.sprintf "Internal Error: invalid type for '%s': found %s for argument %d, expected %s."
        op (string_of_vtype r) arg (string_of_vtype e)
  | Bitrange_index (idx, len) ->
      Printf.sprintf "Internal Error: bitrange index %d is out of range for list of length %d."
        idx len
  | Bitrange_range (hi, lo) ->
      Printf.sprintf "Internal Error: bitrange %d-%d is invalid."
        hi lo
  | No_field f ->
      Printf.sprintf "Internal Error: record does not have field `%s'." f
  | Bitfield_length_mismatch (bf, f, ex, fd) ->
      Printf.sprintf "Internal Error: field `%s' of bitfield `%s' has %d bits instead of %d"
        f bf fd ex
  | Unknown_stdlib (m, f, nargs) ->
      Printf.sprintf "Internal Error: unknown stdlib call `%s.%s' (with %d args)."
        m f nargs
  | Unknown_std_nonterm (nt, nargs) ->
      Printf.sprintf "Internal Error: unknown nonterminal `%s' (with %d attributes)."
        nt nargs
  | Bad_subterm_path (socc, occ) ->
      Printf.sprintf
        "Internal Error: no constructed value at location `%s' of path `%s'."
        (pr_occ socc) (pr_occ occ)
  | Bad_subterm_index (c, idx, occ) ->
      Printf.sprintf
        "Internal Error: invalid term index %d for `%s' in path `%s'."
        idx (str_of_constr c) (pr_occ occ)
  | Unknown_attribute (nt, a) ->
      Printf.sprintf "Internal Error: no attribute `%s' found for non-terminal `%s'"
        a nt
  | Invalid_constructor_value (c, nargs) ->
      Printf.sprintf "Internal Error: illegal constructed value `%s' with %d args."
        (str_of_constr c) nargs

exception Internal_error of Location.t * error

let internal_error l e =
  raise (Internal_error (l, e))
