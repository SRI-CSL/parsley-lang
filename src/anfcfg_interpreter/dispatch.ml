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

(* dispatch table *)

open Interpreter_common
open Values
open Fi
open Interpreter_errors

module DTable = Map.Make (struct type t = string * string
                                 let compare = compare
                          end)
module StringSet = Set.Make(String)

type dtable =
  {mutable dt_mods: StringSet.t;
   mutable dt_0arg: arg0 DTable.t;
   mutable dt_1arg: arg1 DTable.t;
   mutable dt_2arg: arg2 DTable.t;
   mutable dt_3arg: arg3 DTable.t}

(* dispatch table utilities *)

let register_mod (dt: dtable) (m: (module PARSLEY_MOD)) =
  let l = Parsing.Location.ghost_loc in
  let module M = (val m) in
  let mn = M.name in
  (if   StringSet.mem mn dt.dt_mods
   then interpret_error l (Duplicate_module mn));
  List.iter (fun (fn, f) ->
      (if   DTable.mem (mn, fn) dt.dt_0arg
       then interpret_error l (Duplicate_mod_item (mn, fn, 0)));
      dt.dt_0arg <- DTable.add (mn, fn) f dt.dt_0arg
    ) M.arg0_funcs;
  List.iter (fun (fn, f) ->
      (if   DTable.mem (mn, fn) dt.dt_1arg
       then interpret_error l (Duplicate_mod_item (mn, fn, 1)));
      dt.dt_1arg <- DTable.add (mn, fn) f dt.dt_1arg
    ) M.arg1_funcs;
  List.iter (fun (fn, f) ->
      (if   DTable.mem (mn, fn) dt.dt_2arg
       then interpret_error l (Duplicate_mod_item (mn, fn, 2)));
      dt.dt_2arg <- DTable.add (mn, fn) f dt.dt_2arg
    ) M.arg2_funcs;
  List.iter (fun (fn, f) ->
      (if   DTable.mem (mn, fn) dt.dt_3arg
       then interpret_error l (Duplicate_mod_item (mn, fn, 3)));
      dt.dt_3arg <- DTable.add (mn, fn) f dt.dt_3arg
    ) M.arg3_funcs;
  dt.dt_mods <- StringSet.add mn dt.dt_mods

let create_dtable () : dtable =
  {dt_mods = StringSet.empty;
   dt_0arg = DTable.empty;
   dt_1arg = DTable.empty;
   dt_2arg = DTable.empty;
   dt_3arg = DTable.empty}

let update_dtable (dt: dtable) (mods: (module PARSLEY_MOD) list) =
  List.iter (register_mod dt) mods

let find_impl_arg0 (dt: dtable) (m: string) (f: string) : arg0 option =
  DTable.find_opt (m, f) dt.dt_0arg

let find_impl_arg1 (dt: dtable) (m: string) (f: string) : arg1 option =
  DTable.find_opt (m, f) dt.dt_1arg

let find_impl_arg2 (dt: dtable) (m: string) (f: string) : arg2 option =
  DTable.find_opt (m, f) dt.dt_2arg

let find_impl_arg3 (dt: dtable) (m: string) (f: string) : arg3 option =
  DTable.find_opt (m, f) dt.dt_3arg

(* API for actual dispatch table *)

let dtable = create_dtable ()
let initialize_dispatch mods =
  update_dtable dtable mods

let register_impl_arg0 (m: string) (f: string) (impl: arg0) =
  dtable.dt_mods <- StringSet.add m dtable.dt_mods;
  dtable.dt_0arg <- DTable.add (m, f) impl dtable.dt_0arg

let register_impl_arg1 (m: string) (f: string) (impl: arg1) =
  dtable.dt_mods <- StringSet.add m dtable.dt_mods;
  dtable.dt_1arg <- DTable.add (m, f) impl dtable.dt_1arg

let register_impl_arg2 (m: string) (f: string) (impl: arg2) =
  dtable.dt_mods <- StringSet.add m dtable.dt_mods;
  dtable.dt_2arg <- DTable.add (m, f) impl dtable.dt_2arg

let register_impl_arg3 (m: string) (f: string) (impl: arg3) =
  dtable.dt_mods <- StringSet.add m dtable.dt_mods;
  dtable.dt_3arg <- DTable.add (m, f) impl dtable.dt_3arg

let is_lib_mod (m: string) : bool =
  StringSet.mem m dtable.dt_mods

let dispatch_lib lc (m: string) (f: string) (vs: value list)
    : value =
  let nvs = List.length vs in
  let key = m, f in
  if   nvs = 0 && DTable.mem key dtable.dt_0arg
  then let fn = DTable.find key dtable.dt_0arg in
       fn lc
  else if nvs = 1 && DTable.mem key dtable.dt_1arg
  then let fn = DTable.find key dtable.dt_1arg in
       let a0 = List.nth vs 0 in
       fn lc a0
  else if nvs = 2 && DTable.mem key dtable.dt_2arg
  then let fn = DTable.find key dtable.dt_2arg in
       let a0 = List.nth vs 0 in
       let a1 = List.nth vs 1 in
       fn lc a0 a1
  else if nvs = 3 && DTable.mem key dtable.dt_3arg
  then let fn = DTable.find key dtable.dt_3arg in
       let a0 = List.nth vs 0 in
       let a1 = List.nth vs 1 in
       let a2 = List.nth vs 2 in
       fn lc a0 a1 a2
  else let err = Internal_errors.Unknown_stdlib (m, f, nvs) in
       Internal_errors.internal_error lc err
