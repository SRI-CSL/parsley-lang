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

(* bit and bit-vector parsing *)

open Ir
open Values
open State
open Runtime_exceptions

let init_bitwise (v: view) : bitwise =
  {bw_bit_ofs = 0;
   bw_view_id = v.vu_id;
   bw_matched = []}

let enter_bitmode lc (s: state) : state =
  assert (s.st_mode = Mode_normal);
  (* cursor should be at valid offset *)
  let v = s.st_cur_view in
  if   v.vu_ofs >= v.vu_end
  then fault lc (View_bound ("start_bitwise", "end bound exceeded"))
  else let bw = init_bitwise v in
       {s with st_mode = Mode_bitwise bw}

(* accessing bitwise state from bit-mode *)
let get_bitwise (s: state) : bitwise =
  match s.st_mode with
    | Mode_normal ->
        assert false
    | Mode_bitwise bw ->
        (* should be in the same view *)
        let v = s.st_cur_view in
        assert (bw.bw_view_id = v.vu_id);
        bw

let exit_bitmode _lc (s: state) : state =
  let bw = get_bitwise s in
  (* should be byte-aligned *)
  assert (bw.bw_bit_ofs = 0);
  {s with st_mode = Mode_normal}

(* reset the bit-collection buffer *)
let mark_bit_cursor lc (s: state) : state =
  let bw = get_bitwise s in
  let bw = {bw with bw_matched = []} in
  (* cursor should be at valid offset *)
  let v = s.st_cur_view in
  if   v.vu_ofs >= v.vu_end
  then fault lc (View_bound ("set_bit_mark", "end bound exceeded"))
  else {s with st_mode = Mode_bitwise bw}

(* return matched bits *)
let collect_bits _lc (s: state) : bool list * state =
  let bw = get_bitwise s in
  List.rev bw.bw_matched, s

let check_bit_bounds lc op (v: view) (bw: bitwise) n =
  assert (bw.bw_bit_ofs < 8);
  assert (v.vu_ofs <= v.vu_end);
  (* count remaining bits within current byte *)
  let bits_left, ofs =
    if   v.vu_ofs >= v.vu_end
    then (assert (bw.bw_bit_ofs = 0);
          0, v.vu_ofs)
    else 8 - bw.bw_bit_ofs,
         v.vu_ofs + 1 in
  (* add remaining full bytes until end of buffer *)
  let  bits_left = bits_left + 8*(v.vu_end - ofs) in
  if   bits_left < n
  then fault lc (View_bound (op, "end bound exceeded"))

(* Extract `n` bits starting from `ofs` (big-endian): returns list in
   reverse order suitable for accumulation by list prepend *)
let byte_to_nbits (c: char) ofs n : bool list =
  assert (ofs + n <= 8);
  let b = Char.code c in
  let rec loop acc idx =
    if   idx = n then acc
    else let bit = (b lsr (7 - (idx + ofs))) land 0x1 in
         loop ((bit = 0x1) :: acc) (idx + 1) in
  loop [] 0

(* match `n` bits *)
let match_bits lc op (s: state) n : state =
  let bw = get_bitwise s in
  let v = s.st_cur_view in
  check_bit_bounds lc op v bw n;
  (* extract n' bits from specified byte and bit offsets *)
  let buf = v.vu_buf in
  let rec loop (byte_ofs, bit_ofs) n' acc =
    assert (n' >= 0);
    if   n' = 0
    then (byte_ofs, bit_ofs), acc
    else let c = buf.{byte_ofs} in
         let nbits = min n' (8 - bit_ofs) in
         let bits  = byte_to_nbits c bit_ofs nbits in
         let acc   = bits @ acc in
         let byte_ofs, bit_ofs =
           if   nbits < n'
           then byte_ofs + 1, 0
           else if bit_ofs + nbits < 8
           then byte_ofs, bit_ofs + nbits
           else byte_ofs + 1, 0 in
         loop (byte_ofs, bit_ofs) (n' - nbits) acc in
  let (byte_ofs, bit_ofs), acc =
    loop (v.vu_ofs, bw.bw_bit_ofs) n bw.bw_matched in
  (* return updated state *)
  let bw = {bw with bw_bit_ofs = bit_ofs;
                    bw_matched = acc} in
  let v = {v with vu_ofs = byte_ofs} in
  {s with st_mode = Mode_bitwise bw;
          st_cur_view = v}

(* align `n` bits *)
let align_bits lc op (s: state) n : state =
  assert (n mod 8 = 0);
  let bw = get_bitwise s in
  let v  = s.st_cur_view in
  let cur_ofs, nbits = if   bw.bw_bit_ofs > 0
                       then v.vu_ofs + 1, 8 - bw.bw_bit_ofs
                       else v.vu_ofs, 0 in
  let align_ofs = n * ((cur_ofs + n) / n) in
  (* If this is past the end of the buffer, stop at the end of the
     buffer.  Choose not to make it an error to align past the buffer
     end, since we are not `reading' from the buffer.  The next read
     will cause the bounds error. *)
  let align_ofs = min align_ofs v.vu_end in
  let nbits = nbits + 8*(align_ofs - v.vu_end) in
  (* match these bits *)
  match_bits lc op s nbits

(* Bits that match a padding pattern should just be repetitions of the
   pattern *)
let match_padding matched_bits padding =
  let rec loop m p =
    match m, p with
      | mh :: mt, ph :: pt ->
          if   mh = ph
          then loop mt pt
          else false
      | _ ->
          true in
  loop matched_bits padding

let match_bits_bound bits bnd : bool =
  let len = List.length bits in
  match bnd with
    | Cfg.MB_exact n -> len = n
    | Cfg.MB_below n -> len <= n
