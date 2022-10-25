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

(* The standard non-terminals for Parsley *)

open Parsing
open Values
open Runtime_exceptions

type 'a match_result =
  | R_nomatch
  | R_ok  of 'a
  | R_err of Location.t * error

type val_result = (value * view) match_result

let general_byte lc (vu: view) (nt: string) (pred: char -> bool) (to_list: bool)
    : val_result =
  let buf  = !(vu.vu_buf) in
  let ofs  = vu.vu_ofs in
  let vend = vu.vu_end in
  if   ofs >= vend
  then let err = View_bound (nt, "end bound exceeded") in
       R_err (lc, err)
  else let c  = buf_at buf ofs in
       if   pred c
       then let vu = {vu with vu_ofs = ofs + 1} in
            let v = V_char c in
            let v = if   to_list
                    then V_list [v]
                    else v in
            R_ok (v, vu)
       else R_nomatch

let byte lc (vu: view) : val_result =
  general_byte lc vu "Byte" (fun _ -> true) false

let ascii_char_pred (c: char) : bool =
  let cd = Char.code c in
  32 <= cd && cd < 127

let ascii_char lc vu : val_result =
  general_byte lc vu "AsciiChar" ascii_char_pred false

let ascii_char_s lc vu : val_result =
  general_byte lc vu "AsciiCharS" ascii_char_pred true

let hex_char_pred (c: char) : bool =
  let cd = Char.code c in
     (48 <= cd && cd <= 57)
  || (65 <= cd && cd <= 70)
  || (97 <= cd && cd <= 102)

let hex_char lc (vu: view) : val_result =
  general_byte lc vu "HexChar" hex_char_pred false

let hex_char_s lc (vu: view) : val_result =
  general_byte lc vu "HexCharS" hex_char_pred true

let alpha_num_pred (c: char) : bool =
  let cd = Char.code c in
     (48 <= cd && cd <= 57)
  || (65 <= cd && cd <= 90)
  || (97 <= cd && cd <= 122)

let alpha_num lc (vu: view) : val_result =
  general_byte lc vu "AlphaNum" alpha_num_pred false

let alpha_num_s lc (vu: view) : val_result =
  general_byte lc vu "AlphaNumS" alpha_num_pred true

let digit_pred (c: char) : bool =
  let cd = Char.code c in
  48 <= cd && cd <= 57

let digit lc (vu: view) : val_result =
  general_byte lc vu "Digit" digit_pred false

let digit_s lc (vu: view) : val_result =
  general_byte lc vu "DigitS" digit_pred true

let int_of_byte lc (vu: view) (nt: string) : (int * view) match_result =
  let buf  = !(vu.vu_buf) in
  let ofs  = vu.vu_ofs in
  let vend = vu.vu_end in
  if   ofs >= vend
  then let err = View_bound (nt, "end bound exceeded") in
       R_err (lc, err)
  else let i = Char.code (buf_at buf ofs) in
       let vu = {vu with vu_ofs = ofs + 1} in
       R_ok (i, vu)

let uint8 lc (vu: view) : val_result =
  match int_of_byte lc vu "UInt8" with
    | R_ok (i, vu) -> R_ok (V_int (Ast.u8_t, Int64.of_int i), vu)
    | R_nomatch    -> R_nomatch
    | R_err (l, e) -> R_err (l, e)

let int8 lc (vu: view) : val_result =
  match int_of_byte lc vu "Int8" with
    | R_ok (i, vu) -> let i = if   i < 128
                              then i
                              else i - 256 in
                      R_ok (V_int (Ast.i8_t, Int64.of_int i), vu)
    | R_nomatch    -> R_nomatch
    | R_err (l, e) -> R_err (l, e)

(* parses `n` bytes and on success returns
  `i : Int64.t` with `0 <= i < 2^(8*n)`
  with an updated view *)
let int_of_nbytes lc (vu: view) (nt: string) (n: int) (e: endian)
    : (Int64.t * view) match_result =
  let rec iter (acc, vu) idx =
    if   idx = n
    then R_ok (acc, vu)
    else match int_of_byte lc vu nt with
           | R_err (l, e) -> R_err (l, e)
           | R_nomatch    -> R_nomatch
           | R_ok (i, vu) -> let i = Int64.of_int i in
                             let acc, i =
                               match e with
                                 | E_little ->
                                     let i = Int64.shift_left i (8 * idx) in
                                     acc, i
                                 | E_big ->
                                     let acc = Int64.shift_left acc 8 in
                                     acc, i in
                             let acc = Int64.add acc i in
                             iter (acc, vu) (idx + 1) in
  iter (Int64.zero, vu) 0

let impl_uint16 lc (vu: view) (e: endian) : val_result =
  let nt = match e with
      | E_little -> "UInt16.Little"
      | E_big    -> "UInt16.Big" in
  match int_of_nbytes lc vu nt 2 e with
    | R_err (l, e) -> R_err (l, e)
    | R_nomatch    -> R_nomatch
    | R_ok (i, vu) -> R_ok (V_int (Ast.u16_t, i), vu)

let impl_int16 lc (vu: view) (e: endian) : val_result =
  let nt = match e with
      | E_little -> "Int16.Little"
      | E_big    -> "Int16.Big" in
  match int_of_nbytes lc vu nt 2 e with
    | R_err (l, e) -> R_err (l, e)
    | R_nomatch    -> R_nomatch
    | R_ok (i, vu) -> let i = if   Int64.compare i 32768L < 0
                              then i
                              else Int64.sub i 65536L in
                      R_ok (V_int (Ast.i16_t, i), vu)

let impl_uint32 lc (vu: view) (e: endian) : val_result =
  let nt = match e with
      | E_little -> "UInt32.Little"
      | E_big    -> "UInt32.Big" in
  match int_of_nbytes lc vu nt 4 e with
    | R_err (l, e) -> R_err (l, e)
    | R_nomatch    -> R_nomatch
    | R_ok (i, vu) -> R_ok (V_int (Ast.u32_t, i), vu)

let impl_int32 lc (vu: view) (e: endian) : val_result =
  let nt = match e with
      | E_little -> "Int32.Little"
      | E_big    -> "Int32.Big" in
  match int_of_nbytes lc vu nt 4 e with
    | R_err (l, e) -> R_err (l, e)
    | R_nomatch    -> R_nomatch
    | R_ok (i, vu) -> let i = if   Int64.compare i 2147483648L < 0
                              then i
                              else Int64.sub i 4294967296L in
                      R_ok (V_int (Ast.i32_t, i), vu)

(* Int64.t is signed, and hence this can be negative *)
let impl_uint64 lc (vu: view) (e: endian) : val_result =
  let nt = match e with
      | E_little -> "UInt64.Little"
      | E_big    -> "UInt64.Big" in
  match int_of_nbytes lc vu nt 8 e with
    | R_err (l, e) -> R_err (l, e)
    | R_nomatch    -> R_nomatch
    | R_ok (i, vu) -> R_ok (V_int (Ast.u64_t, i), vu)

let impl_int64 lc (vu: view) (e: endian) : val_result =
  let nt = match e with
      | E_little -> "Int64.Little"
      | E_big    -> "Int64.Big" in
  match int_of_nbytes lc vu nt 8 e with
    | R_err (l, e) -> R_err (l, e)
    | R_nomatch    -> R_nomatch
    | R_ok (i, vu) -> R_ok (V_int (Ast.i64_t, i), vu)

let get_int_endian lc nt (s, v) : endian =
  match s, v with
    | "endian", V_constr ((Anfcfg.Anf.M_stdlib, "endian", "Big"), []) ->
        E_big
    | "endian", V_constr ((Anfcfg.Anf.M_stdlib, "endian", "Little"), []) ->
        E_little
    | "endian", V_constr (c, args) ->
        let nargs = List.length args in
        let err =
          Internal_errors.Invalid_constructor_value (c, nargs) in
        internal_error lc err
    | "endian", _ ->
        let f   = Printf.sprintf "%s(endian:)" nt in
        let t = T_adt "endian" in
        let err =
          Internal_errors.Type_error (f, 1, vtype_of v, t) in
        internal_error lc err
    | a, _ ->
        let err =
          Internal_errors.Unknown_attribute (nt, a) in
        internal_error lc err

let wrap int_impl lc vu pv : val_result =
  let e = get_int_endian lc "UInt16" pv in
  int_impl lc vu e

module DTable = Map.Make (struct type t = string
                                 let compare = compare
                          end)
type arg0 = Location.t -> view -> val_result
type arg1 = Location.t -> view -> string * value -> val_result

type dtable =
  {dt_0arg: arg0 DTable.t;
   dt_1arg: arg1 DTable.t}

let mk_dtable () : dtable =
  let arg0s = [
      (* atomic values *)
      "Byte",       byte;
      "AsciiChar",  ascii_char;
      "HexChar",    hex_char;
      "AlphaNum",   alpha_num;
      "Digit",      digit;
      (* composable with regular expressions *)
      "AsciiCharS", ascii_char_s;
      "HexCharS",   hex_char_s;
      "AlphaNumS",  alpha_num_s;
      "DigitS",     digit_s;
      (* binary integer types *)
      "UInt8",      uint8;
      "Int8",       int8;
    ] in
  let arg1s = [
      (* binary integer types with endianness *)
      "Int16",      wrap impl_int16;
      "UInt16",     wrap impl_uint16;
      "Int32",      wrap impl_int32;
      "UInt32",     wrap impl_uint32;
      "Int64",      wrap impl_int64;
      "UInt64",     wrap impl_uint64;
    ] in
  {dt_0arg = DTable.of_seq (List.to_seq arg0s);
   dt_1arg = DTable.of_seq (List.to_seq arg1s)}

let dtable: dtable = mk_dtable ()

let is_std_nonterm s =
  DTable.mem s dtable.dt_0arg || DTable.mem s dtable.dt_1arg

let dispatch_stdlib lc (nt: string) (vu: view) (vs: (string * value) list)
    : val_result =
  let nvs = List.length vs in
  if   nvs = 0 && DTable.mem nt dtable.dt_0arg
  then let fn = DTable.find nt dtable.dt_0arg in
       fn lc vu
  else if nvs = 1 && DTable.mem nt dtable.dt_1arg
  then let fn = DTable.find nt dtable.dt_1arg in
       let a0 = List.nth vs 0 in
       fn lc vu a0
  else let err = Internal_errors.Unknown_std_nonterm (nt, nvs) in
       internal_error lc err
