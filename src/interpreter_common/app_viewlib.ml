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

(* Application side support for views.

   This is to support initialization and extension of views from
   external data sources. *)

open Runtime_exceptions

(* The pause handler specifies handler functions that handle each
   kind of pause.  The `require_refill` handler is called with a
   minimum number of bytes to read from the input source to continue
   the parse. *)
type pause_handler =
  {ph_require_refill: (int -> bytes option) option}

let refill_from_channel (ch: in_channel) (need: int)
    : bytes option =
  let buf = Bytes.make need '\000' in
  let rec loop ofs rem =
    let rd = input ch buf ofs rem in
    if   rd >= rem
    then Some buf
    else loop (ofs + rd) (rem - rd) in
  loop 0 need

let from_static_file filename : Values.view * pause_handler =
  let fd  = Unix.openfile filename [O_RDONLY] 0 in
  let buf =
    Unix.map_file fd Bigarray.char Bigarray.c_layout false [|(-1)|] in
  let buf  = Bigarray.array1_of_genarray buf in
  let size = (Unix.fstat fd).Unix.st_size in
  let view = Viewlib.view_of_mmapped_buf filename buf size in
  view, {ph_require_refill = None}

let from_string (name: string) (data: string)
    : Values.view * pause_handler =
  let buf  = Bytes.of_string data in
  let size = String.length data in
  let view = Viewlib.view_of_byte_buf name buf size in
  view,  {ph_require_refill = None}

let from_channel (name: string) (ch: in_channel) (init_size: int)
    : Values.view * pause_handler =
  let buf = match refill_from_channel ch init_size with
      | None ->
          let lc = Parsing.Location.ghost_loc in
          let err = Buffer_creation_failure name in
          fault lc err
      | Some buf ->
          buf in
  let size = Bytes.length buf in
  let view = Viewlib.view_of_byte_buf name buf size in
  view, {ph_require_refill = Some (refill_from_channel ch)}
