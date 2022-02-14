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

module Location = Parsing.Location

type errormsg = {
  _start: Location.pos;
  _end: Location.pos;
  _ghost: bool;
  _reason: string;
}[@@deriving to_yojson];;

let mk_json_errormsg t msg =
  let err = {
    _start = Location.position_to_pos t.loc_start;
    _end = Location.position_to_pos t.loc_end;
    _ghost = t.loc_ghost;
    _reason = msg
  } in
  errormsg_to_yojson inner

(* `bt`  contains the backtrace if this is a debugging build.
   `loc` contains the location of the error.
   `msg` is the error message from the compiler. *)
let handle_exception bt loc msg =
   if !Options.json_out
   then (
      Printf.fprintf stderr "%s" (Yojson.Safe.to_string (mk_json_errormsg loc msg));
      exit 1
   )
   else (
      let content = Location.content_of_loc loc in
      Printf.printf "%s\n" bt;
      Printf.fprintf stderr "%s%s: %s\n" content (Location.str_of_loc loc) msg;
      exit 1
   )
   
