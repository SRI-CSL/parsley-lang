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

open Typing
open Values
open Runtime_exceptions
open Internal_errors

(* builtin operators *)

let int_uminus lc (v: value) : value =
  match v with
    | V_int i -> V_int (Int64.neg i)
    | _ -> internal_error (Type_error (lc, "uminus", 1, vtype_of v, T_int))

let bool_not lc (v: value) : value =
  match v with
    | V_bool b -> V_bool (not b)
    | _ -> internal_error (Type_error (lc, "not", 1, vtype_of v, T_bool))

let bitvector_negate lc (v: value) : value =
  match v with
    | V_bitvector bl -> V_bitvector (List.map not bl)
    | _ -> internal_error (Type_error (lc, "negate", 1, vtype_of v, T_bitvector))

let int_plus lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_int (Int64.add l r)
    | V_int _, _       -> internal_error (Type_error (lc, "+", 2, vtype_of r, T_int))
    | _, _             -> internal_error (Type_error (lc, "+", 1, vtype_of l, T_int))

let int_minus lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_int (Int64.sub l r)
    | V_int _, _       -> internal_error (Type_error (lc, "-", 2, vtype_of r, T_int))
    | _, _             -> internal_error (Type_error (lc, "-", 1, vtype_of l, T_int))

let int_mul lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_int (Int64.mul l r)
    | V_int _, _       -> internal_error (Type_error (lc, "*", 2, vtype_of r, T_int))
    | _, _             -> internal_error (Type_error (lc, "*", 1, vtype_of l, T_int))

let int_mod lc (l: value) (r: value) : value =
  match l, r with
    | V_int _, V_int r when r = Int64.zero -> fault (Division_by_zero lc)
    | V_int l, V_int r -> V_int (Int64.rem l r)
    | V_int _, _       -> internal_error (Type_error (lc, "%", 2, vtype_of r, T_int))
    | _, _             -> internal_error (Type_error (lc, "%", 1, vtype_of l, T_int))

let int_div lc (l: value) (r: value) : value =
  match l, r with
    | V_int _, V_int r when r = Int64.zero -> fault (Division_by_zero lc)
    | V_int l, V_int r -> V_int (Int64.div l r)
    | V_int _, _       -> internal_error (Type_error (lc, "/", 2, vtype_of r, T_int))
    | _, _             -> internal_error (Type_error (lc, "/", 1, vtype_of l, T_int))

let less_than lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_bool (Int64.compare l r < 0)
    | V_int _, _       -> internal_error (Type_error (lc, "<", 2, vtype_of r, T_int))
    | _, _             -> internal_error (Type_error (lc, "<", 1, vtype_of l, T_int))

let greater_than lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_bool (Int64.compare l r > 0)
    | V_int _, _       -> internal_error (Type_error (lc, ">", 2, vtype_of r, T_int))
    | _, _             -> internal_error (Type_error (lc, ">", 1, vtype_of l, T_int))

let le_than lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_bool (Int64.compare l r <= 0)
    | V_int _, _       -> internal_error (Type_error (lc, "<=", 2, vtype_of r, T_int))
    | _, _             -> internal_error (Type_error (lc, "<=", 1, vtype_of l, T_int))

let ge_than lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_bool (Int64.compare l r >= 0)
    | V_int _, _       -> internal_error (Type_error (lc, ">=", 2, vtype_of r, T_int))
    | _, _             -> internal_error (Type_error (lc, ">=", 1, vtype_of l, T_int))

let bool_and lc (l: value) (r: value) : value =
  match l, r with
    | V_bool l, V_bool r -> V_bool (l && r)
    | V_bool _, _        -> internal_error (Type_error (lc, "&&", 2, vtype_of r, T_bool))
    | _, _               -> internal_error (Type_error (lc, "&&", 1, vtype_of l, T_bool))

let bool_or lc (l: value) (r: value) : value =
  match l, r with
    | V_bool l, V_bool r -> V_bool (l || r)
    | V_bool _, _        -> internal_error (Type_error (lc, "||", 2, vtype_of r, T_bool))
    | _, _               -> internal_error (Type_error (lc, "||", 1, vtype_of l, T_bool))

let bv_not lc (v: value) : value =
  match v with
    | V_bitvector bv -> V_bitvector (List.map not bv)
    | _              -> internal_error (Type_error (lc, "~", 1, vtype_of v, T_bitvector))

let bv_or lc (l: value) (r: value) : value =
  match l, r with
    | V_bitvector l, V_bitvector r when List.length l != List.length r ->
        fault (Length_mismatch (lc, "|_b", List.length l, List.length r))
    | V_bitvector l, V_bitvector r ->
        V_bitvector (List.map2 (||) l r)
    | V_bitvector _, _ ->
        internal_error (Type_error (lc, "|_b", 2, vtype_of r, T_bitvector))
    | _, _ ->
        internal_error (Type_error (lc, "|_b", 1, vtype_of l, T_bitvector))

let bv_and lc (l: value) (r: value) : value =
  match l, r with
    | V_bitvector l, V_bitvector r when List.length l != List.length r ->
        fault (Length_mismatch (lc, "&_b", List.length l, List.length r))
    | V_bitvector l, V_bitvector r ->
        V_bitvector (List.map2 (&&) l r)
    | V_bitvector _, _ ->
        internal_error (Type_error (lc, "&_b", 2, vtype_of r, T_bitvector))
    | _, _ ->
        internal_error (Type_error (lc, "&_b", 1, vtype_of l, T_bitvector))

let bit_extract lc (l: bool list) (hi: int) (lo: int) =
  let rec rextract l acc idx =
    if   idx > hi
    then acc
    else let b = List.nth l idx in
         rextract l (b :: acc) (idx + 1) in
  let len = List.length l in
  if hi >= len
  then internal_error (Bitrange_index (lc, hi, len))
  else if lo >= len
  then internal_error (Bitrange_index (lc, lo, len))
  else rextract l [] lo

let bv_bitrange lc (l: value) (hi: int) (lo: int) : value =
  match l with
    | V_bitvector l ->
        V_bitvector (bit_extract lc l hi lo)
    | _ ->
        internal_error (Type_error (lc, "bitrange", 1, vtype_of l, T_bitvector))

let mk_bitfield_type (bfi: TypingEnvironment.bitfield_info) =
  let rcd = List.map (fun (f, _, _) -> f, T_bitvector) bfi.bf_fields in
  T_record rcd

let rec_of_bits lc (r: string) (l: value) (bfi: TypingEnvironment.bitfield_info)
    : value =
  match l with
    | V_bitvector l ->
        let fs = List.fold_left (fun acc (f, hi, lo) ->
                     (f, V_bitvector (bit_extract lc l hi lo)) :: acc
                   ) [] bfi.bf_fields in
        V_record fs
    | _ ->
        let op = Printf.sprintf "%s->record" r in
        let ty = mk_bitfield_type bfi in
        internal_error (Type_error (lc, op, 1, vtype_of l, ty))

let bits_of_rec lc (r: string) (l: value) (bfi: TypingEnvironment.bitfield_info)
    : value =
  let op = Printf.sprintf "%s->bits" r in
  match l with
    | V_record rv ->
        (* Note that we assume the fields are in increasing order,
           since they are sorted before registered into the type
           environment. *)
        let l =
          List.fold_left (fun acc (f, hi, lo) ->
              match List.assoc_opt f rv with
                  | None ->
                      internal_error (No_field (lc, f))
                  | Some (V_bitvector l) ->
                      let ex = List.length l in
                      let fd = hi - lo + 1 in
                      if   ex = fd
                      then l @ acc
                      else let err = Bitfield_length_mismatch (lc, r, f, ex, fd) in
                           internal_error err
                  | Some v ->
                      internal_error (Type_error (lc, op, 1, vtype_of v, T_bitvector))
            ) [] bfi.bf_fields in
        assert (List.length l = bfi.bf_length);
        V_bitvector l
    | _ ->
        let ty = mk_bitfield_type bfi in
        internal_error (Type_error (lc, op, 1, vtype_of l, ty))

(* pure boolean helpers for equality and inequality *)
let rec eq lc op l r =
  match l, r with
    | V_unit, V_unit               -> true
    | V_bool l, V_bool r           -> l = r
    | V_bit l, V_bit r             -> l = r
    | V_int l, V_int r             -> l = r
    | V_string l, V_string r       -> l = r
    | V_bitvector l, V_bitvector r -> l = r

    | V_option None, V_option None -> true
    | V_option (Some l), V_option (Some r) -> eq lc op l r
    | V_option _, V_option _       -> false

    | V_list ls, V_list rs | V_tuple ls, V_tuple rs ->
        eqs lc op true ls rs

    | V_constr ((tl, cl), ls), V_constr ((tr, cr), rs) ->
        if tl != tr
        then internal_error (Type_error (lc, op, 2, vtype_of l, vtype_of r))
        else if cl != cr
        then false
        else eqs lc op true ls rs

    | V_view {vu_id = l; _}, V_view {vu_id = r; _} ->
        (* only compare their ids *)
        l = r

    | V_set [], V_set [] | V_map [], V_map [] ->
        true
    | V_set ls, V_set rs ->
        eqs lc op true ls rs

    | V_map ls, V_map rs ->
        (* Before comparing, we need to normalize by sorting the keys. *)
        let srt m =
          List.sort (fun (kl, _) (kr, _) -> compare kl kr) m in
        let sls, srs = srt ls, srt rs in
        eqm lc op true sls srs
    | _, _  ->
        internal_error (Type_error (lc, op, 2, vtype_of l, vtype_of r))

and eqs lc op acc ls rs =
  (* we don't short circuit to catch type errors, though this won't
     catch type errors if lengths are different *)
  match ls, rs with
    | [], [] -> acc
    | hl :: tl, hr :: tr -> eqs lc op (acc && eq lc op hl hr) tl tr
    | _, _ -> false
and eqm lc op acc lm rm =
  (* we don't short circuit to catch type errors, though this won't
     catch type errors if lengths are different *)
  match lm, rm with
    | [], [] ->
        acc
    | (lk, lv) :: tl, (rk, rv) :: tr ->
        eqm lc op (acc && eq lc op lk rk && eq lc op lv rv) tl tr
    | _, _ ->
        false

let equals lc (l: value) (r: value) : value =
  V_bool (eq lc "=" l r)

let not_equals lc (l: value) (r: value) : value =
  V_bool (not (eq lc "!=" l r))

let record_field lc (l: value) (f: string) : value =
  match l with
    | V_record fs ->
        (match List.assoc_opt f fs with
           | Some v -> v
           | None -> internal_error (No_field (lc, f)))
    | _ ->
        internal_error (Type_error (lc, "." ^ f, 1, vtype_of l, T_record [f, T_empty]))

let constr_match lc (l: value) (c: string * string) : value =
  match l with
    | V_constr (c', _) ->
        V_bool (c = c')
    | _ ->
        internal_error (Type_error (lc, "~~", 1, vtype_of l, T_adt (c, [])))
