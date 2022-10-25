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

module Sample_counters : PARSLEY_MOD = struct
  (* An external module implementing isize counters named by isize integers. *)
  module IntMap = Map.Make(struct type t = Ast.num_t * Int64.t
                                  let compare = compare
                           end)
  let counters = ref IntMap.empty

  (* Increments a specified counter if it exists, or initializes it to
     1 if it doesn't.  Returns an option containing the previous value
     if the counter existed. *)
  let incr_counter lc (v: value) : value =
    match v with
      | V_int (it, i) when it = Ast.isize_t ->
          let k = it, i in
          let ret, map = match IntMap.find_opt k !counters  with
              | Some c ->
                  Some (V_int (Ast.isize_t, c)), IntMap.add k (Int64.succ c) !counters
              | None   ->
                  None, IntMap.add k 1L !counters in
          counters := map;
          V_option ret
      | _ ->
          let err = Type_error ("Counters.incr_counter", 1,
                                vtype_of v, T_int Ast.isize_t) in
          internal_error lc err

  (* Decrements a specified counter if it exists, or initializes it to
     -1 if it doesn't.  Returns an option containing the previous
     value if the counter existed. *)
  let decr_counter lc (v: value) : value =
    match v with
      | V_int (it, i) when it = Ast.isize_t ->
          let k = it, i in
          let ret, map = match IntMap.find_opt k !counters  with
              | Some c ->
                  Some (V_int (Ast.isize_t, c)), IntMap.add k (Int64.pred c) !counters
              | None   ->
                  None, IntMap.add k (-1L) !counters in
          counters := map;
          V_option ret
      | _ ->
          let err = Type_error ("Counters.decr_counter", 1,
                                vtype_of v, T_int Ast.isize_t) in
          internal_error lc err

  (* Resets a specified counter to 0, creating it if it did not exist.
     Returns an option containing the previous value if the counter
     existed. *)
  let reset_counter lc (v: value) : value =
    match v with
      | V_int (it, i) when it = Ast.isize_t ->
          let k = it, i in
          let ret, map = match IntMap.find_opt k !counters  with
              | Some c ->
                  Some (V_int (Ast.isize_t, c)), IntMap.add k 0L !counters
              | None   ->
                  None, IntMap.add k 0L !counters in
          counters := map;
          V_option ret
      | _ ->
          let err = Type_error ("Counters.reset_counter", 1,
                                vtype_of v, T_int Ast.isize_t) in
          internal_error lc err

  (* Returns the value of the specified counter, if it exists. *)
  let get_counter lc (v: value) : value =
    match v with
      | V_int (it, i) when it = Ast.isize_t ->
          let k = it, i in
          let ret = match IntMap.find_opt k !counters  with
              | Some c ->
                  Some (V_int (Ast.isize_t, c))
              | None   ->
                  None in
          V_option ret
      | _ ->
          let err = Type_error ("Counters.get_counter", 1,
                                vtype_of v, T_int Ast.isize_t) in
          internal_error lc err

  let name = "Counters"

  let arg0_funcs = [
    ]
  let arg1_funcs = [
      "incr_counter",  incr_counter;
      "decr_counter",  decr_counter;
      "reset_counter", reset_counter;
      "get_counter",   get_counter
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
    (module Sample_counters);
  ]
