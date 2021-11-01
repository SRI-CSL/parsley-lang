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

open Values
open Parsleylib

let from_file filename : value =
  let fd  = Unix.openfile filename [O_RDONLY] 0 in
  let buf =
    Unix.map_file fd Bigarray.char Bigarray.c_layout false [|(-1)|] in
  let buf  = Bigarray.array1_of_genarray buf in
  let id   = PView.next_id () in
  let size = (Unix.fstat fd).Unix.st_size in
  (* Ensure size from Unix is consistent with Bigarray. *)
  assert (size = ViewBuf.size buf);
  let vu =
    {vu_buf    = buf;
     (* TODO: use (Unix.realpath filename) once OCaml 4.13 is more
        commonly installed *)
     vu_source = Src_file filename;
     vu_id     = id;
     vu_start  = 0;
     vu_ofs    = 0;
     vu_end    = size} in
  V_view vu
