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
open Ir

let msg m loc =
  Printf.sprintf m (Location.str_of_loc loc)

module Internal_errors = struct
  (* These errors indicate internal bugs. *)
  type error =
    | Type_error of Location.t * string * int * vtype * vtype
    | Not_implemented of Location.t * string
    | No_binding_for_read of Location.t * Anf.varid
    | No_binding_for_write of Anf.var
    | Bitrange_index of Location.t * int * int
    | No_field of Location.t * string
    | Bitfield_length_mismatch of Location.t * string * string * int * int
    | Duplicate_function_binding of Location.t * string
    | Function_arity of Location.t * string * int * int
    | Unknown_stdlib of Location.t * string * string * int
    | Bad_subterm_path of Location.t * Ir.Anf.occurrence * Ir.Anf.occurrence
    | Bad_subterm_index of Location.t * (string * string) * int * Ir.Anf.occurrence
    | Pattern_match_failure of Location.t * Anf.var

  let error_msg =
    let pr_occ = Ir.Anf_printer.string_of_occurrence in
    function
    | Type_error (l, op, arg, r, e) ->
        msg "%s:\n INTERNAL ERROR: invalid type for '%s': found %s for argument %d, expected %s."
          l op (string_of_vtype r) arg (string_of_vtype e)
    | Not_implemented (l, s) ->
        msg "%s:\n INTERNAL ERROR: Not implemented error: '%s'." l s
    | No_binding_for_read (l, v) ->
        msg "%s:\n INTERNAL ERROR: Variable '%s:%d' is not bound." l (fst v) (snd v)
    | No_binding_for_write v ->
        msg "%s:\n INTERNAL ERROR: Cannot assign to unbound variable '%s:%d'."
          Anf.(v.v_loc) (fst Anf.(v.v)) (snd Anf.(v.v))
    | Bitrange_index (l, idx, len) ->
        msg "%s:\n INTERNAL ERROR: bitrange index %d is out of range for list of length %d."
          l idx len
    | No_field (l, f) ->
        msg "%s:\n INTERNAL ERROR: record does not have field `%s'." l f
    | Bitfield_length_mismatch (lc, bf, f, ex, fd) ->
        msg "%s:\n INTERNAL ERROR: field `%s' of bitfield `%s' has %d bits instead of %d"
          lc f bf fd ex
    | Duplicate_function_binding (lc, f) ->
        msg "%s:\n INTERNAL ERROR: function `%s' is already bound."
          lc f
    | Function_arity (lc, f, nps, npvs) ->
        msg "%s:\n INTERNAL ERROR: function `%s' expected %d args, got %d instead."
          lc f nps npvs
    | Unknown_stdlib (lc, m, f, nargs) ->
        msg "%s:\n INTERNAL ERROR: unknown stdlib call `%s.%s' (with %d args)."
          lc m f nargs
    | Bad_subterm_path (lc, socc, occ) ->
        msg
          "%s:\n INTERNAL ERROR: no constructed value at location `%s' of path `%s'."
          lc (pr_occ socc) (pr_occ occ)
    | Bad_subterm_index (lc, (t, c), idx, occ) ->
        msg
          "%s:\n INTERNAL ERROR: invalid term index %d for `%s::%s' in path `%s'."
          lc idx t c (pr_occ occ)
    | Pattern_match_failure (lc, v) ->
        msg "%s:\n INTERNAL ERROR: no patterns matched for `%s:%d'."
          lc (fst Anf.(v.v)) (snd Anf.(v.v))
end

type error =
  | Division_by_zero of Location.t
  | Length_mismatch of Location.t * string * int * int
  | Index_bound of Location.t * int * int
  | Unsafe_operation_failure of Location.t * string
  | Invalid_argument of Location.t * string * string
  | Overflow of Location.t * string
  | View_bound of Location.t * string * string
  | Internal of Internal_errors.error

exception Runtime_exception of error

let fault e =
  raise (Runtime_exception e)

let internal_error e =
  raise (Runtime_exception (Internal e))

let error_msg = function
  | Division_by_zero l ->
      msg "%s:\n Division by zero." l
  | Length_mismatch (l, op, ll, lr) ->
      msg "%s:\n Mismatched lengths for '%s': %d vs %d."
        l op ll lr
  | Index_bound (l, idx, len) ->
      msg "%s:\n Index %d is out of bounds for list of length %d."
        l idx len
  | Unsafe_operation_failure (l, op) ->
      msg "%s:\n Unsafe operation '%s' failed." l op
  | Invalid_argument (l, op, s) ->
      msg "%s:\n Invalid argument to '%s': %s" l op s
  | Overflow (l, op) ->
      msg "%s:\n Operation '%s' overflowed." l op
  | View_bound (l, op, m) ->
      msg "%s:\n View operation '%s' went out of bounds: %s." l op m
  | Internal e ->
      Internal_errors.error_msg e
