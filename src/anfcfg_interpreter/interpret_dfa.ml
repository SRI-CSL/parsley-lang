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

(* Runs a regular DFA on input bytes and return the result (bytes
   matched and an updated view) if any. *)

open Anfcfg.Dfa
open Values

let run (dfa: DFA.t) (v: view) : (value * view) option =
  let buf   = !(v.vu_buf) in
  let vend  = v.vu_end in
  let start = v.vu_ofs in
  assert (start <= vend);
  let s = DFA.start dfa in
  let try_accept s ofs bytes =
    if   DFA.accept dfa s
    then let vu    = {v with vu_ofs = ofs} in
         let bytes = List.rev_map (fun b -> V_char b) bytes in
         Some (V_list bytes, vu)
    else None in
  let rec loop s ofs bytes =
    (* `s` is the current state, and `ofs` is the (potentially
       invalid) offset where the next byte will be read.

       The current state might have a transition as well as be an
       accepting state.  For greedy matching, check for a transition
       first if possible before trying to accept. *)
    if   ofs >= vend
    then try_accept s ofs bytes
    else let c = buf_at buf ofs in
         match DFA.next dfa (s, c) with
           | None   -> try_accept s ofs bytes
           | Some s -> loop s (ofs + 1) (c :: bytes) in
  (* run the DFA *)
  loop s start []

(* Byte extracter. *)
let extract_bytes buf start len : value list =
  assert (len > 0);
  let rec loop acc idx =
    if   idx < start
    then acc
    else let acc = V_char (buf_at buf idx) :: acc in
         loop acc (idx - 1) in
  loop [] (start + len - 1)

(* Special case for scanning for a tag. *)
let scan_forward (v: view) (tag: string) : (value * view) option =
  let tlen = String.length tag in
  let vlen = v.vu_end - v.vu_ofs in
  let buf  = !(v.vu_buf) in
  (* inner loop *)
  let match_tag base =
    assert (v.vu_ofs <= base);
    assert (base + tlen <= v.vu_end);
    let rec loop idx =
      if   tag.[idx] = buf_at buf (base + idx)
      then let idx = idx + 1 in
           if   idx >= tlen
           then true
           else loop idx
      else false in
    loop 0 in
  (* outer loop, incrementing to go forwards *)
  let scan () =
    let bases = vlen - tlen + 1 in
    let rec loop b =
      let  ofs = v.vu_ofs + b in
      if   match_tag ofs
      then Some ofs
      else let b = b + 1 in
           if   b > bases
           then None
           else loop b in
    loop 0 in
  assert (vlen >= 0);
  if   vlen < tlen
  then None
  else match scan () with
         | None     -> None
         | Some ofs -> (* include tag bytes in match value *)
                       let mlen  = (ofs - v.vu_ofs) + tlen in
                       let bytes = extract_bytes buf v.vu_ofs mlen in
                       (* cursor is positioned on last tag byte *)
                       let vu = {v with vu_ofs = ofs + tlen - 1} in
                       Some (V_list bytes, vu)

let scan_backward (v: view) (tag: string) : (value * view) option =
  let tlen = String.length tag in
  let vlen = v.vu_ofs - v.vu_start + 1 in
  let buf  = !(v.vu_buf) in
  (* inner loop, matches forwards *)
  let match_tag base =
    assert (v.vu_start <= base);
    assert (base + tlen - 1 <= v.vu_ofs);
    let rec loop idx =
      if   tag.[idx] = buf_at buf (base + idx)
      then let idx = idx + 1 in
           if   idx >= tlen
           then true
           else loop idx
      else false in
    loop 0 in
  (* outer loop, decrementing to go backwards *)
  let scan () =
    let bases = vlen - tlen in
    let rec loop b =
      let  ofs = v.vu_start + b in
      if   match_tag ofs
      then Some ofs
      else let b = b - 1 in
           if   b < 0
           then None
           else loop b in
    loop bases in
  assert (vlen >= 0);
  if   vlen < tlen
  then None
  else match scan () with
         | None     -> None
         | Some ofs -> (* include tag bytes in match value *)
                       let mlen  = v.vu_ofs - ofs + 1 in
                       let bytes = extract_bytes buf ofs mlen in
                       (* cursor is positioned on first tag byte *)
                       let vu = {v with vu_ofs = ofs} in
                       Some (V_list bytes, vu)

let scan (view: view) (tag: string) (dir: Parsing.Ast.scan_direction)
    : (value * view) option =
  match dir with
    | Parsing.Ast.Scan_forward  -> scan_forward  view tag
    | Parsing.Ast.Scan_backward -> scan_backward view tag
