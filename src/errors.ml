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

(* `bt`  contains the backtrace if this is a debugging build.
   `loc` contains the location of the error.
   `msg` is the error message from the compiler. *)
let handle_exception bt loc msg =
  if   Location.is_ghost loc
  then Printf.fprintf stderr "%s\n" msg
  else (let content = Location.content_of_loc loc in
        Printf.printf "%s\n" bt;
        Printf.fprintf stderr "%s%s: %s\n" content (Location.str_of_loc loc) msg);
  exit Cmdliner.Cmd.Exit.some_error
