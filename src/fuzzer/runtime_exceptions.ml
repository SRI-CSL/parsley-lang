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
open Flow
open Ir

module Internal_errors = struct
  (* These errors indicate internal bugs. *)
  type error =
    | Type_error of string * int * vtype * vtype
    | Not_implemented of string
    | No_binding_for_read of Anf.varid
    | No_binding_for_write of Anf.var
    | Bitrange_index of int * int
    | Bitrange_range of int (* hi *) * int (* lo *)
    | No_field of string
    | No_field_specified
    | Bitfield_length_mismatch of string * string * int * int
    | Duplicate_function_binding of string
    | Function_arity of string * int * int
    | Unknown_stdlib of string * string * int
    | Unknown_std_nonterm of string * int
    | Bad_subterm_path of Ir.Anf.occurrence * Ir.Anf.occurrence
    | Bad_subterm_index of (string * string) * int * Ir.Anf.occurrence
    | Pattern_match_failure of Anf.var
    | View_stack_underflow
    | Bitsbound_check of string
    | Failcont_stack_underflow
    | Unexpected_failcont of Cfg.label * Cfg.label
    | No_nonterm_entry of Ast.ident
    | Unknown_attribute of string * string
    | Invalid_constructor_value of (string * string) * int
    | No_block_for_label of Label.label

  let error_msg =
    let pr_occ = Ir.Anf_printer.string_of_occurrence in
    function
    | Type_error (op, arg, r, e) ->
        Printf.sprintf "Internal Error: invalid type for '%s': found %s for argument %d, expected %s."
          op (string_of_vtype r) arg (string_of_vtype e)
    | Not_implemented s ->
        Printf.sprintf "Internal Error: Not implemented error: '%s'." s
    | No_binding_for_read v ->
        Printf.sprintf "Internal Error: Variable '%s#%d' is not bound." (fst v) (snd v)
    | No_binding_for_write v ->
        Printf.sprintf "Internal Error: Cannot assign to unbound variable '%s#%d'."
          (fst Anf.(v.v)) (snd Anf.(v.v))
    | Bitrange_index (idx, len) ->
        Printf.sprintf "Internal Error: bitrange index %d is out of range for list of length %d."
          idx len
    | Bitrange_range (hi, lo) ->
        Printf.sprintf "Internal Error: bitrange %d-%d is invalid."
          hi lo
    | No_field f ->
        Printf.sprintf "Internal Error: record does not have field `%s'." f
    | No_field_specified ->
        Printf.sprintf "Internal Error: no field specified."
    | Bitfield_length_mismatch (bf, f, ex, fd) ->
        Printf.sprintf "Internal Error: field `%s' of bitfield `%s' has %d bits instead of %d"
          f bf fd ex
    | Duplicate_function_binding f ->
        Printf.sprintf "Internal Error: function `%s' is already bound." f
    | Function_arity (f, nps, npvs) ->
        Printf.sprintf "Internal Error: function `%s' expected %d args, got %d instead."
          f nps npvs
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
    | Bad_subterm_index ((t, c), idx, occ) ->
        Printf.sprintf
          "Internal Error: invalid term index %d for `%s::%s' in path `%s'."
          idx t c (pr_occ occ)
    | Pattern_match_failure v ->
        Printf.sprintf "Internal Error: no patterns matched for `%s#%d'."
          (fst Anf.(v.v)) (snd Anf.(v.v))
    | View_stack_underflow ->
        "Internal Error: the view stack underflowed."
    | Bitsbound_check m ->
        Printf.sprintf "Internal Error: bits-bound check failed: %s" m
    | Failcont_stack_underflow ->
        Printf.sprintf "Internal Error: failcont stack underflow"
    | Unexpected_failcont (l, le) ->
        Printf.sprintf "Internal Error: unexpected failcont label %s, expected %s"
          (Cfg.string_of_label l) (Cfg.string_of_label le)
    | No_nonterm_entry nt ->
        Printf.sprintf "Internal Error: no non-terminal entry found for `%s'"
          (Location.value nt)
    | Unknown_attribute (nt, a) ->
        Printf.sprintf "Internal Error: no attribute `%s' found for non-terminal `%s'"
          a nt
    | Invalid_constructor_value ((t, c), nargs) ->
        Printf.sprintf "Internal Error: illegal constructed value `%s::%s' with %d args."
          t c nargs
    | No_block_for_label l ->
        Printf.sprintf "Internal Error: no block found for label `%s'."
          (Label.to_string l)
end

type error =
  | Division_by_zero
  | Length_mismatch of string * int * int
  | Index_bound of int * int
  | Unsafe_operation_failure of string
  | Invalid_argument of string * string
  | Overflow of string
  | View_bound of string * string
  | Internal of Internal_errors.error

exception Runtime_exception of Location.t * error

let fault l e =
  raise (Runtime_exception (l, e))

let internal_error l e =
  raise (Runtime_exception (l, (Internal e)))

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
  | Internal e ->
      Internal_errors.error_msg e
