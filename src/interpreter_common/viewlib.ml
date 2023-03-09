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

(* library support for views *)

open Parsing
open Values
open Runtime_exceptions
open Internal_errors

module PView = struct
  (* Incremented and used as id for every new view value created. *)
  let view_id = ref Int64.zero

  let next_id () =
    let id = !view_id in
    view_id := Int64.succ !view_id;
    id

  (* Copy the view but give it a new id. Note that the pointer to the
     backing buffer is copied, so that modifications like extensions to
     the buffer are immediately visible to the clones.  Extensions are
     safe since existing views will remain valid.  But buffer pruning
     will need to handled carefully, since it could invalidate
     existing views.
   *)
  let clone_view v =
    {vu_buf    = v.vu_buf;
     vu_source = v.vu_source;
     vu_id     = next_id ();
     vu_kind   = v.vu_kind;
     vu_start  = v.vu_start;
     vu_ofs    = v.vu_ofs;
     vu_end    = v.vu_end}

  (* Remaining accessible bytes in view. *)
  let remaining v =
    v.vu_end - v.vu_ofs

  (* Cursor offset into view. *)
  let cursor v =
    v.vu_ofs - v.vu_start

  (* Size of the current view. *)
  let size v =
    v.vu_end - v.vu_start

  (* Whether this is a `root` view, i.e. a view that spans the entire
     underlying parse buffer. *)
  let is_root v =
    size v = buf_size !(v.vu_buf)

  (* Kind of view. *)
  let is_closed v =
    v.vu_kind = VK_closed
  let is_open v =
    v.vu_kind = VK_open

  let restrict lc (_v: view) (v: value) (o: value) (l: value) : value =
    match v, o, l with
      | V_view v, V_int (on, o), V_int (ln, l)
           when on = ln && ln = Ast.usize_t ->
          (* Extend `v` before restriction bounds checks. *)
          extend_view v;
          (* We should ideally never get negative offsets below, but
             since the backing type of `usize_t` is a signed
             `Int64.t`, we do need to check. *)
          if   Int64.compare o Int64.zero < 0
          then fault lc (Invalid_argument ("View.restrict", "negative offset"))
          else if Int64.compare l Int64.zero < 0
          then fault lc (Invalid_argument ("View.restrict", "negative length"))
          else begin
              assert (0 <= v.vu_start && v.vu_start <= v.vu_ofs);
              assert (v.vu_ofs <= v.vu_end);
              assert (v.vu_end <= buf_size !(v.vu_buf));
              let o, l = Int64.to_int o, Int64.to_int l in
              if   v.vu_ofs + o + l > v.vu_end
              then fault lc (View_bound ("View.restrict", "end bound exceeded"))
              else V_view {v with vu_id    = next_id ();
                                  vu_start = v.vu_ofs + o;
                                  vu_ofs   = v.vu_ofs + o;
                                  vu_end   = v.vu_ofs + o + l;
                                  (* restricted views are always closed *)
                                  vu_kind  = VK_closed}
            end
      | V_view _, V_int (on, _), _ when on = Ast.usize_t ->
          internal_error lc (Type_error ("View.restrict", 3, vtype_of l, T_int Ast.usize_t))
      | V_view _, _, _ ->
          internal_error lc (Type_error ("View.restrict", 2, vtype_of o, T_int Ast.usize_t))
      | _, _, _ ->
          internal_error lc (Type_error ("View.restrict", 1, vtype_of v, T_view))

  let restrict_from lc (_v: view) (v: value) (o: value) : value =
    match v, o with
      | V_view v, V_int (on, o) when on = Ast.usize_t ->
          (* Extend `v` before restriction bounds checks. *)
          extend_view v;
          (* See above note on `usize_t` being negative. *)
          if   Int64.compare o Int64.zero < 0
          then fault lc (Invalid_argument ("View.restrict_from", "negative offset"))
          else begin
              assert (0 <= v.vu_start && v.vu_start <= v.vu_ofs);
              assert (v.vu_ofs <= v.vu_end);
              assert (v.vu_end <= buf_size !(v.vu_buf));
              let o = Int64.to_int o in
              if   v.vu_ofs + o >= v.vu_end
              then fault lc (View_bound ("View.restrict_from", "end bound exceeded"))
              else V_view {v with vu_id    = next_id ();
                                  vu_start = v.vu_ofs + o;
                                  vu_ofs   = v.vu_ofs + o;
                                  (* inherit the vu_kind *) }
            end
      | V_view _, _ ->
          internal_error lc (Type_error ("View.restrict_from", 2, vtype_of o, T_int Ast.usize_t))
      | _, _ ->
          internal_error lc (Type_error ("View.restrict_from", 1, vtype_of v, T_view))

  let clone lc (_v: view) (v: value) : value =
    match v with
      | V_view vu ->
          V_view (clone_view vu)
      | _ ->
          internal_error lc (Type_error ("View.clone", 1, vtype_of v, T_view))

  let get_base _lc (v: view) : value =
    let vu = clone_view v in
    let vu = {vu with vu_ofs = vu.vu_start} in
    V_view vu

  let get_current _lc (v: view) : value =
    (* retain the view id *)
    V_view v

  let get_cursor lc (_v: view) (v: value) : value =
    match v with
      | V_view vu ->
          V_int (Ast.usize_t, Int64.of_int (cursor vu))
      | _ ->
          internal_error lc (Type_error ("View.clone", 1, vtype_of v, T_view))

  let get_remaining lc (_v: view) (v: value) : value =
    match v with
      | V_view vu ->
          (* extend `vu` before computing bound *)
          extend_view vu;
          V_int (Ast.usize_t, Int64.of_int (remaining vu))
      | _ ->
          internal_error lc (Type_error ("View.clone", 1, vtype_of v, T_view))

  let get_current_cursor lc (v: view) : value =
    get_cursor lc v (V_view v)

  let get_current_remaining lc (v: view) : value =
    get_remaining lc v (V_view v)
end

module DTable = Map.Make (struct type t = string * string
                                 let compare = compare
                          end)
type arg0 = Location.t -> view -> value
type arg1 = Location.t -> view -> value -> value
type arg2 = Location.t -> view -> value -> value -> value
type arg3 = Location.t -> view -> value -> value -> value -> value

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
      ("View", "get_current_remaining"), PView.get_current_remaining;
    ] in
  let arg1s = [
      ("View", "get_cursor"),         PView.get_cursor;
      ("View", "get_remaining"),      PView.get_remaining;
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

let dispatch_viewlib lc (m: string) (f: string) (cv: view) (vs: value list)
    : value =
  let nvs = List.length vs in
  let key = m, f in
  if   nvs = 0 && DTable.mem  key dtable.dt_0arg
  then let fn = DTable.find key dtable.dt_0arg in
       fn lc cv
  else if nvs = 1 && DTable.mem  key dtable.dt_1arg
  then let fn = DTable.find key dtable.dt_1arg in
       let a0 = List.nth vs 0 in
       fn lc cv a0
  else if nvs = 2 && DTable.mem  key dtable.dt_2arg
  then let fn = DTable.find key dtable.dt_2arg in
       let a0 = List.nth vs 0 in
       let a1 = List.nth vs 1 in
       fn lc cv a0 a1
  else if nvs = 3 && DTable.mem  key dtable.dt_3arg
  then let fn = DTable.find key dtable.dt_3arg in
       let a0 = List.nth vs 0 in
       let a1 = List.nth vs 1 in
       let a2 = List.nth vs 2 in
       fn lc cv a0 a1 a2
  else let err = Internal_errors.Unknown_stdlib (m, f, nvs) in
       internal_error lc err

let view_of_mmapped_buf filename buf size =
  let id   = PView.next_id () in
  let mbuf = Buf_mmap buf in
  (* Ensure size from Unix is consistent with Bigarray. *)
  assert (size = buf_size mbuf);
  {vu_buf    = ref mbuf;
   (* TODO: use (Unix.realpath filename) once OCaml 4.13 is more
      commonly installed *)
   vu_source = Src_file filename;
   vu_id     = id;
   vu_kind   = VK_closed;
   vu_start  = 0;
   vu_ofs    = 0;
   vu_end    = size}

let view_of_byte_buf name buf size =
  let id   = PView.next_id () in
  let mbuf = Buf_bytes buf in
  (* Ensure size is consistent with Bigarray. *)
  assert (size = buf_size mbuf);
  {vu_buf    = ref mbuf;
   vu_source = Src_file name;
   vu_id     = id;
   vu_kind   = VK_open;
   vu_start  = 0;
   vu_ofs    = 0;
   vu_end    = size}
