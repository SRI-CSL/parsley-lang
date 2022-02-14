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

open Lexing

type t =
  {loc_start: position;
   loc_end:   position;
   loc_ghost: bool}

let init lexbuf fname =
  lexbuf.lex_curr_p <-
    {pos_fname = fname;
     pos_lnum  = 1;
     pos_bol   = 0;
     pos_cnum  = 0}

let curr lexbuf =
  {loc_start = lexbuf.lex_start_p;
   loc_end   = lexbuf.lex_curr_p;
   loc_ghost = false}

let _mk_loc b e g =
  {loc_start = b;
   loc_end   = e;
   loc_ghost = g}

let mk_loc b e = _mk_loc b e false

let ghost_loc = _mk_loc Lexing.dummy_pos Lexing.dummy_pos true

let extent loc1 loc2 =
  mk_loc
    (if loc1.loc_ghost then loc2.loc_start else loc1.loc_start)
    (if loc2.loc_ghost then loc1.loc_end else loc2.loc_end)

let loc_or_ghost = function
  | Some l -> l
  | None   -> ghost_loc

let get_pos_info pos =
  pos.pos_fname, pos.pos_lnum, pos.pos_cnum - pos.pos_bol

let get_start loc =
  loc.loc_start

let get_end loc =
  loc.loc_end

let is_ghost loc =
  loc.loc_ghost

let loc_of_curr_lex lexbuf =
  {loc_start = lexbuf.lex_curr_p;
   loc_end   = lexbuf.lex_curr_p;
   loc_ghost = false}

(* formatted to start a sentence *)
let str_of_loc loc =
  let file, line, startchar = get_pos_info loc.loc_start in
  let endchar =
    loc.loc_end.pos_cnum - loc.loc_start.pos_cnum + startchar in
  Printf.sprintf "File \"%s\", line %d, characters %d-%d"
                 file line startchar endchar

(* formatted to fit in the middle of a sentence *)
let str_of_file_loc loc =
  let file, line, startchar = get_pos_info loc.loc_start in
  let endchar =
    loc.loc_end.pos_cnum - loc.loc_start.pos_cnum + startchar in
  Printf.sprintf "file \"%s\", line %d, characters %d-%d"
                 file line startchar endchar

type 'a loc =
  {pelem: 'a;
   ploc:  t}

let mk_loc_val a l =
  {pelem = a;
   ploc  = l}

let mk_ghost a =
  {pelem = a;
   ploc = ghost_loc}

let value l = l.pelem

let loc l = l.ploc

(* the source lines for a location *)

let raw_lines_of_loc loc =
  let from = loc.loc_start in
  let upto = loc.loc_end in
  let chan = open_in from.pos_fname in
  seek_in chan from.pos_bol;
  let rec get_lines acc () =
    let stl = pos_in chan in
    let l   = input_line chan in
    let etl = pos_in chan in
    let acc = ((stl, etl), l) :: acc in
    if   etl < upto.pos_cnum
    then get_lines acc ()
    else List.rev acc in
  get_lines [] ()

let lines_of_loc loc =
  if   loc.loc_ghost
  then None
  else try Some (raw_lines_of_loc loc) with | _ -> None

let str_of_content loc lines =
  let b    = Buffer.create 256 in
  let from = loc.loc_start.pos_cnum in
  let upto = loc.loc_end.pos_cnum in
  (* Prune lines to avoid showing more than 5 in a snippet. *)
  let lines =
    let  nlines = List.length lines in
    if   nlines <= 5
    then lines
    else (* add a filler line that will not highlight *)
      let pos = loc.loc_end.pos_cnum, loc.loc_start.pos_bol in
      let filler = pos, "[some lines omitted]\n" in
      [List.nth lines 0; List.nth lines 1; filler;
       List.nth lines (nlines - 2); List.nth lines (nlines - 1)] in
  List.iter (fun ((s, e), l) ->
      Buffer.add_string b l;
      (* add highlighting appropriately *)
      if   s <= upto && from <= e
      then (
        Buffer.add_string b "\n";
        (* prefix *)
        if   s < from
        then Buffer.add_string b (String.make (from - s) ' ');
        (* highlight *)
        let f = max s from in
        let t = min e upto in
        if   f <= t
        then let hilen = max (t - f) 1 in
             Buffer.add_string b (String.make hilen '^');
        (* suffix *)
        if   s < from || f <= t
        then Buffer.add_string b "\n";
      )
    ) lines;
  Buffer.contents b

let content_of_loc loc =
  match lines_of_loc loc with
    | None    -> ""
    | Some ls -> str_of_content loc ls
