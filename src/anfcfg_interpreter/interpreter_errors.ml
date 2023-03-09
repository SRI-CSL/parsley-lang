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
open Flow
open Anfcfg

(* These errors indicate internal bugs. *)
type error =
  | No_binding_for_read of Anf_common.varid
  | No_mod_binding_for_read of string * string
  | No_binding_for_write of Anf.var
  | No_field_specified
  | Duplicate_function_binding of string
  | Duplicate_mod_value_binding of string * string
  | Function_arity of string * int * int
  | Pattern_match_failure of Anf.var
  | View_stack_underflow
  | Bitsbound_check of string
  | Failcont_stack_underflow
  | Unexpected_failcont of Cfg.label * Cfg.label
  | No_nonterm_entry of Ast.ident
  | No_block_for_label of Label.label
  | Duplicate_module of string
  | Duplicate_mod_item of string * string * int

let error_msg =
  function
  | No_binding_for_read v ->
      Printf.sprintf "Internal Error: Variable '%s#%d' is not bound." (fst v) (snd v)
  | No_binding_for_write v ->
      Printf.sprintf "Internal Error: Cannot assign to unbound variable '%s#%d'."
        (fst Anf.(v.v)) (snd Anf.(v.v))
  | No_mod_binding_for_read (m, v) ->
      Printf.sprintf "Internal Error: No value found for '%s.%s'." m v
  | No_field_specified ->
      Printf.sprintf "Internal Error: no field specified."
  | Duplicate_function_binding f ->
      Printf.sprintf "Internal Error: function `%s' is already bound." f
  | Duplicate_mod_value_binding (m, v) ->
      Printf.sprintf "Internal Error: module value `%s.%s' is already bound." m v
  | Function_arity (f, nps, npvs) ->
      Printf.sprintf "Internal Error: function `%s' expected %d args, got %d instead."
        f nps npvs
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
  | No_block_for_label l ->
      Printf.sprintf "Internal Error: no block found for label `%s'."
        (Label.to_string l)
  | Duplicate_module m ->
      Printf.sprintf "Internal Error: module `%s' is already registered."
        m
  | Duplicate_mod_item (m, f, n) ->
      Printf.sprintf "Internal Error: duplicate %d-argument item `%s' in module `%s'."
        n m f

exception Interpreter_error of Location.t * error

let interpret_error l e =
  raise (Interpreter_error (l, e))
