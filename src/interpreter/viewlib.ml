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

(* initialization of views from external data *)

open Parsing
open Values
open State
open Runtime_exceptions
open Internal_errors

module PView = struct
  (* incremented and used as id for every new view value created *)
  let view_id = ref Int64.zero

  let next_id () =
    let id = !view_id in
    view_id := Int64.succ !view_id;
    id

  (* copy the view but give it a new id *)
  let clone_view v =
    {vu_buf    = v.vu_buf;
     vu_source = v.vu_source;
     vu_id     = next_id ();
     vu_start  = v.vu_start;
     vu_ofs    = v.vu_ofs;
     vu_end    = v.vu_end}

  let restrict lc (_s: state) (v: value) (o: value) (l: value) : value =
    match v, o, l with
      | V_view v, V_int o, V_int l ->
          if Int64.compare o Int64.zero < 0
          then fault (Invalid_argument (lc, "View.restrict", "negative offset"))
          else if Int64.compare l Int64.zero < 0
          then fault (Invalid_argument (lc, "View.restrict", "negative length"))
          else begin
              assert (0 <= v.vu_start && v.vu_start <= v.vu_ofs);
              assert (v.vu_ofs <= v.vu_end);
              assert (v.vu_end <= ViewBuf.size v.vu_buf);
              let o, l = Int64.to_int o, Int64.to_int l in
              if v.vu_ofs + o + l >= v.vu_end
              then fault (View_bound (lc, "View.restrict", "end bound exceeded"))
              else V_view {v with vu_id    = next_id ();
                                  vu_start = v.vu_ofs + o;
                                  vu_ofs   = 0;
                                  vu_end   = v.vu_ofs + o + l}
            end
      | V_view _, V_int _, _ ->
          internal_error (Type_error (lc, "View.restrict", 3, vtype_of l, T_int))
      | V_view _, _, _ ->
          internal_error (Type_error (lc, "View.restrict", 2, vtype_of o, T_int))
      | _, _, _ ->
          internal_error (Type_error (lc, "View.restrict", 1, vtype_of v, T_view))

  let restrict_from lc (_s: state) (v: value) (o: value) : value =
    match v, o with
      | V_view v, V_int o ->
          if Int64.compare o Int64.zero < 0
          then fault (Invalid_argument (lc, "View.restrict_from", "negative offset"))
          else begin
              assert (0 <= v.vu_start && v.vu_start <= v.vu_ofs);
              assert (v.vu_ofs <= v.vu_end);
              assert (v.vu_end <= ViewBuf.size v.vu_buf);
              let o = Int64.to_int o in
              if   v.vu_ofs + o >= v.vu_end
              then fault (View_bound (lc, "View.restrict_from", "end bound exceeded"))
              else V_view {v with vu_id    = next_id ();
                                  vu_start = v.vu_ofs + o;
                                  vu_ofs   = 0}
            end
      | V_view _, _ ->
          internal_error (Type_error (lc, "View.restrict_from", 2, vtype_of o, T_int))
      | _, _ ->
          internal_error (Type_error (lc, "View.restrict_from", 1, vtype_of v, T_view))

  let clone lc (_s: state) (v: value) : value =
    match v with
      | V_view vu ->
          V_view (clone_view vu)
      | _ ->
          internal_error (Type_error (lc, "View.clone", 1, vtype_of v, T_view))

  let get_base _lc (s: state) : value =
    let vu = clone_view s.st_cur_view in
    let vu = {vu with vu_ofs = vu.vu_start} in
    V_view vu

  let get_current _lc (s: state) : value =
    (* retain the view id *)
    V_view s.st_cur_view

  let get_current_cursor _lc (s: state) : value =
    let vu = s.st_cur_view in
    V_int (Int64.of_int vu.vu_ofs)
end

module DTable = Map.Make (struct type t = string * string
                                 let compare = compare
                          end)
type arg0 = Location.t -> state -> value
type arg1 = Location.t -> state -> value -> value
type arg2 = Location.t -> state -> value -> value -> value
type arg3 = Location.t -> state -> value -> value -> value -> value

type dtable =
  {dt_0arg: arg0 DTable.t;
   dt_1arg: arg1 DTable.t;
   dt_2arg: arg2 DTable.t;
   dt_3arg: arg3 DTable.t}

let mk_dtable () : dtable =
  let arg0s = [
      ("View", "get_base"),           PView.get_base;
      ("View", "get_current"),        PView.get_current;
      ("View", "get_current_cursor"), PView.get_current_cursor;
    ] in
  let arg1s = [
      ("View", "clone"),              PView.clone;
    ] in
  let arg2s = [
      ("View", "restrict_from"),      PView.restrict_from;
    ] in
  let arg3s = [
      ("View", "restrict"),           PView.restrict;
    ] in
  {dt_0arg = DTable.of_seq (List.to_seq arg0s);
   dt_1arg = DTable.of_seq (List.to_seq arg1s);
   dt_2arg = DTable.of_seq (List.to_seq arg2s);
   dt_3arg = DTable.of_seq (List.to_seq arg3s)}

let dtable: dtable = mk_dtable ()

let dispatch_viewlib lc (m: string) (f: string) (s: state) (vs: value list)
    : value =
  let nvs = List.length vs in
  let key = m, f in
  if   nvs = 0 && DTable.mem  key dtable.dt_0arg
  then let fn = DTable.find key dtable.dt_0arg in
       fn lc s
  else if nvs = 1 && DTable.mem  key dtable.dt_1arg
  then let fn = DTable.find key dtable.dt_1arg in
       let a0 = List.nth vs 0 in
       fn lc s a0
  else if nvs = 2 && DTable.mem  key dtable.dt_2arg
  then let fn = DTable.find key dtable.dt_2arg in
       let a0 = List.nth vs 0 in
       let a1 = List.nth vs 1 in
       fn lc s a0 a1
  else if nvs = 3 && DTable.mem  key dtable.dt_3arg
  then let fn = DTable.find key dtable.dt_3arg in
       let a0 = List.nth vs 0 in
       let a1 = List.nth vs 1 in
       let a2 = List.nth vs 2 in
       fn lc s a0 a1 a2
  else let err = Internal_errors.Unknown_stdlib (lc, m, f, nvs) in
       internal_error err

(* helpers for runtime *)

let from_file filename : view =
  let fd  = Unix.openfile filename [O_RDONLY] 0 in
  let buf =
    Unix.map_file fd Bigarray.char Bigarray.c_layout false [|(-1)|] in
  let buf  = Bigarray.array1_of_genarray buf in
  let id   = PView.next_id () in
  let size = (Unix.fstat fd).Unix.st_size in
  (* Ensure size from Unix is consistent with Bigarray. *)
  assert (size = ViewBuf.size buf);
  {vu_buf    = buf;
   (* TODO: use (Unix.realpath filename) once OCaml 4.13 is more
      commonly installed *)
   vu_source = Src_file filename;
   vu_id     = id;
   vu_start  = 0;
   vu_ofs    = 0;
   vu_end    = size}

let from_string (name: string) (data: string) : view =
  let buf = Bigarray.Array1.of_array Bigarray.char Bigarray.c_layout
              (Array.of_seq (String.to_seq data)) in
  let id   = PView.next_id () in
  let size = String.length data in
  (* Ensure size from Unix is consistent with Bigarray. *)
  assert (size = ViewBuf.size buf);
  {vu_buf    = buf;
   vu_source = Src_file name;
   vu_id     = id;
   vu_start  = 0;
   vu_ofs    = 0;
   vu_end    = size}

let set_view lc (s: state) (v: value) : state =
  match v with
    | V_view vu ->
        {s with st_cur_view = vu}
    | _ ->
        internal_error (Type_error (lc, "set-view", 1, vtype_of v, T_view))

let set_pos lc (s: state) (v: value) : state =
  match v with
    | V_int i ->
        let i = Int64.to_int i in
        let vu = s.st_cur_view in
        if   i < 0
        then fault (View_bound (lc, "set-pos", "negative offset specified"))
        else if vu.vu_start + i >= vu.vu_end
        then fault (View_bound (lc, "set-pos", "end bound exceeded"))
        else let vu = {vu with vu_ofs = vu.vu_start + i} in
             {s with st_cur_view = vu}
    | _ ->
        internal_error (Type_error (lc, "set-pos", 1, vtype_of v, T_int))
