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

open Ir.Dfa
open Values

let run (dfa: DFA.t) (v: view) : (value * view) option =
  let buf   = v.vu_buf in
  let vend  = v.vu_end in
  let start = v.vu_ofs in
  assert (start <= vend);
  let s = DFA.start dfa in
  let rec loop s ofs bytes =
    (* `s` is the current state, and `ofs` is the (potentially
       invalid) offset where the next byte will be read *)
    if   DFA.accept dfa s
    then let vu    = {v with vu_ofs = ofs} in
         let bytes = List.rev_map (fun b -> V_char b) bytes in
         Some (V_list bytes, vu)
    else if  ofs >= vend
    then None (* non-accepting state with no input *)
    else let c = buf.{ofs} in
         match DFA.next dfa (s, c) with
           | None   -> None
           | Some s -> loop s (ofs + 1) (c :: bytes) in
  (* run the DFA *)
  loop s start []
