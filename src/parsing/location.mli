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

type t

val init: Lexing.lexbuf -> string -> unit
val curr: Lexing.lexbuf -> t
val str_of_curr_pos: Lexing.lexbuf -> string

val ghost_loc : t
val mk_loc: Lexing.position -> Lexing.position -> t
val extent: t -> t -> t
val loc_or_ghost: t option -> t
val get_start:    t -> Lexing.position
val get_end:      t -> Lexing.position

type 'a loc

val mk_loc_val:  'a -> t -> 'a loc
val mk_ghost:    'a -> 'a loc
val value:       'a loc -> 'a
val loc:         'a loc -> t

val str_of_loc:      t -> string (* full location, including file name *)
val str_of_file_loc: t -> string (* location without file name *)
