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

(* Implementations of external/foreign functions. *)

open Parsing
open Fi
open Values
open Runtime_exceptions
open Internal_errors

(* The external (i.e. external to Parsley, and implemented in OCaml)
   functions are grouped by their number of input arguments, and
   collected into a module implementing the `PARSLEY_MOD` interface.
 *)
module Sample_ext : PARSLEY_MOD = struct
  (* internal implementation detail *)
  let length lc (v: value) : value =
    match v with
      | V_list l ->
          V_int (Ast.usize_t, Int64.of_int (List.length l))
      | _ ->
          let err = Type_error ("Sample_ext.length", 1,
                                vtype_of v, T_list T_empty) in
          internal_error lc err

  (* external API *)
  let name = "Sample_ext"  (* The module name specified in the `ocaml`
                              language binding tag in the `foreign`
                              section of the Parsley source . *)
  let arg0_funcs = [
    ]
  let arg1_funcs = [
      "length", length     (* The function name specified in the
                              `ocaml` language binding tag in the
                              `foreign` section of the Parsley
                              source. *)
    ]
  let arg2_funcs = [
    ]
  let arg3_funcs = [
    ]
end

(* Modules that implement the `PARSLEY_MOD` interface need to be added
   to the below list to be processed by the interpreter. *)
let ext_mods : (module PARSLEY_MOD) list = [
    (* add modules to this list *)
    (module Sample_ext);
  ]
