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

(*  Adapted from:                                                         *)
(*  Mini, a type inference engine based on constraint solving.            *)
(*  Copyright (C) 2006. Fran�ois Pottier, Yann R�gis-Gianas               *)
(*  and Didier R�my.                                                      *)

(** This module provides a common formatting interface to
    pretty-print in LaTeX, raw text or module Format mode. *)

type formatter_output =
  {out:       string -> int -> int -> unit;
   flush:     unit -> unit;
   newline:   unit -> unit;
   spaces:    int -> unit;
   with_tags: bool;
   open_tag:  Format.stag -> unit;
   close_tag: Format.stag -> unit;
   margin:    int}

type output =
  | Channel of out_channel
  | Buffer  of Buffer.t

type mode =
  | Txt       of output
  | Formatter of formatter_output

val output_string: output -> string -> unit

val flush: output -> unit
