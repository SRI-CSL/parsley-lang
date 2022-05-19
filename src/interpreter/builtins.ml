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
    | _ -> internal_error lc (Type_error ("uminus", 1, vtype_of v, T_int))

let bool_not lc (v: value) : value =
  match v with
    | V_bool b -> V_bool (not b)
    | _ -> internal_error lc (Type_error ("not", 1, vtype_of v, T_bool))

let bitvector_negate lc (v: value) : value =
  match v with
    | V_bitvector bl -> V_bitvector (List.map not bl)
    | _ -> internal_error lc (Type_error ("negate", 1, vtype_of v, T_bitvector))

let int_plus lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_int (Int64.add l r)
    | V_int _, _       -> internal_error lc (Type_error ("+", 2, vtype_of r, T_int))
    | _, _             -> internal_error lc (Type_error ("+", 1, vtype_of l, T_int))

let int_minus lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_int (Int64.sub l r)
    | V_int _, _       -> internal_error lc (Type_error ("-", 2, vtype_of r, T_int))
    | _, _             -> internal_error lc (Type_error ("-", 1, vtype_of l, T_int))

let int_mul lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_int (Int64.mul l r)
    | V_int _, _       -> internal_error lc (Type_error ("*", 2, vtype_of r, T_int))
    | _, _             -> internal_error lc (Type_error ("*", 1, vtype_of l, T_int))

let int_mod lc (l: value) (r: value) : value =
  match l, r with
    | V_int _, V_int r when r = Int64.zero -> fault lc Division_by_zero
    | V_int l, V_int r -> V_int (Int64.rem l r)
    | V_int _, _       -> internal_error lc (Type_error ("%", 2, vtype_of r, T_int))
    | _, _             -> internal_error lc (Type_error ("%", 1, vtype_of l, T_int))

let int_div lc (l: value) (r: value) : value =
  match l, r with
    | V_int _, V_int r when r = Int64.zero -> fault lc Division_by_zero
    | V_int l, V_int r -> V_int (Int64.div l r)
    | V_int _, _       -> internal_error lc (Type_error ("/", 2, vtype_of r, T_int))
    | _, _             -> internal_error lc (Type_error ("/", 1, vtype_of l, T_int))

let less_than lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_bool (Int64.compare l r < 0)
    | V_int _, _       -> internal_error lc (Type_error ("<", 2, vtype_of r, T_int))
    | _, _             -> internal_error lc (Type_error ("<", 1, vtype_of l, T_int))

let greater_than lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_bool (Int64.compare l r > 0)
    | V_int _, _       -> internal_error lc (Type_error (">", 2, vtype_of r, T_int))
    | _, _             -> internal_error lc (Type_error (">", 1, vtype_of l, T_int))

let le_than lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_bool (Int64.compare l r <= 0)
    | V_int _, _       -> internal_error lc (Type_error ("<=", 2, vtype_of r, T_int))
    | _, _             -> internal_error lc (Type_error ("<=", 1, vtype_of l, T_int))

let ge_than lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_bool (Int64.compare l r >= 0)
    | V_int _, _       -> internal_error lc (Type_error (">=", 2, vtype_of r, T_int))
    | _, _             -> internal_error lc (Type_error (">=", 1, vtype_of l, T_int))

let bool_and lc (l: value) (r: value) : value =
  match l, r with
    | V_bool l, V_bool r -> V_bool (l && r)
    | V_bool _, _        -> internal_error lc (Type_error ("&&", 2, vtype_of r, T_bool))
    | _, _               -> internal_error lc (Type_error ("&&", 1, vtype_of l, T_bool))

let bool_or lc (l: value) (r: value) : value =
  match l, r with
    | V_bool l, V_bool r -> V_bool (l || r)
    | V_bool _, _        -> internal_error lc (Type_error ("||", 2, vtype_of r, T_bool))
    | _, _               -> internal_error lc (Type_error ("||", 1, vtype_of l, T_bool))

let bv_not lc (v: value) : value =
  match v with
    | V_bitvector bv -> V_bitvector (List.map not bv)
    | _              -> internal_error lc (Type_error ("~", 1, vtype_of v, T_bitvector))

let bv_or lc (l: value) (r: value) : value =
  match l, r with
    | V_bitvector l, V_bitvector r when List.length l != List.length r ->
        fault lc (Length_mismatch ("|_b", List.length l, List.length r))
    | V_bitvector l, V_bitvector r ->
        V_bitvector (List.map2 (||) l r)
    | V_bitvector _, _ ->
        internal_error lc (Type_error ("|_b", 2, vtype_of r, T_bitvector))
    | _, _ ->
        internal_error lc (Type_error ("|_b", 1, vtype_of l, T_bitvector))

let bv_and lc (l: value) (r: value) : value =
  match l, r with
    | V_bitvector l, V_bitvector r when List.length l != List.length r ->
        fault lc (Length_mismatch ("&_b", List.length l, List.length r))
    | V_bitvector l, V_bitvector r ->
        V_bitvector (List.map2 (&&) l r)
    | V_bitvector _, _ ->
        internal_error lc (Type_error ("&_b", 2, vtype_of r, T_bitvector))
    | _, _ ->
        internal_error lc (Type_error ("&_b", 1, vtype_of l, T_bitvector))

let bit_extract lc (l: bool list) (hi: int) (lo: int) =
  let len = List.length l in
  if   hi >= len
  then internal_error lc (Bitrange_index (hi, len))
  else if lo >= len
  then internal_error lc (Bitrange_index (lo, len))
  else if lo > hi
  then internal_error lc (Bitrange_range (hi, lo))
  else field_of_bitvector l hi lo

let bv_bitrange lc (l: value) (hi: int) (lo: int) : value =
  match l with
    | V_bitvector l ->
        V_bitvector (bit_extract lc l hi lo)
    | _ ->
        internal_error lc (Type_error ("bitrange", 1, vtype_of l, T_bitvector))

let mk_bitfield_type (bfi: TypingEnvironment.bitfield_info) =
  let rcd = List.map (fun (f, _) -> f, T_bitvector) bfi.bf_fields in
  T_record rcd

let rec_of_bits lc (r: string) (l: value) (bfi: TypingEnvironment.bitfield_info)
    : value =
  match l with
    | V_bitvector l ->
        let fs = List.fold_left (fun acc (f, (hi, lo)) ->
                     (f, V_bitvector (bit_extract lc l hi lo)) :: acc
                   ) [] bfi.bf_fields in
        V_record fs
    | _ ->
        let op = Printf.sprintf "%s->record" r in
        let ty = mk_bitfield_type bfi in
        internal_error lc (Type_error (op, 1, vtype_of l, ty))

let bits_of_rec lc (r: string) (l: value) (bfi: TypingEnvironment.bitfield_info)
    : value =
  let op = Printf.sprintf "%s->bits" r in
  match l with
    | V_record rv ->
        (* Note that we assume the fields are in increasing order,
           since they are sorted before registered into the type
           environment. *)
        let l =
          List.fold_left (fun acc (f, (hi, lo)) ->
              match List.assoc_opt f rv with
                  | None ->
                      internal_error lc (No_field f)
                  | Some (V_bitvector l) ->
                      let ex = List.length l in
                      let fd = hi - lo + 1 in
                      if   ex = fd
                      then l @ acc
                      else let err = Bitfield_length_mismatch (r, f, ex, fd) in
                           internal_error lc err
                  | Some v ->
                      internal_error lc (Type_error (op, 1, vtype_of v, T_bitvector))
            ) [] bfi.bf_fields in
        assert (List.length l = bfi.bf_length);
        V_bitvector l
    | _ ->
        let ty = mk_bitfield_type bfi in
        internal_error lc (Type_error (op, 1, vtype_of l, ty))

(* pure boolean helpers for equality and inequality *)
let mand b b' =
  match b, b' with
    | Ok b, Ok b' -> Ok (b && b')
    | Error e, _
    | _, Error e  -> Error e

let rec eq lc op l r : (bool, error) result =
  match l, r with
    | V_unit, V_unit               -> Ok true
    | V_bool l, V_bool r           -> Ok (l = r)
    | V_bit l, V_bit r             -> Ok (l = r)
    | V_char l, V_char r           -> Ok (l = r)
    | V_int l, V_int r             -> Ok (l = r)
    | V_float l, V_float r         -> Ok (l = r)
    | V_string l, V_string r       -> Ok (l = r)
    | V_bitvector l, V_bitvector r -> Ok (l = r)

    | V_bitfield (li, lv), V_bitfield (ri, rv)
         when
           let li = {li with bf_fields = List.sort compare li.bf_fields} in
           let ri = {ri with bf_fields = List.sort compare ri.bf_fields} in
           li = ri ->
        Ok (lv = rv)

    | V_option None, V_option None         -> Ok true
    | V_option (Some l), V_option (Some r) -> eq lc op l r
    | V_option _, V_option _               -> Ok false

    | V_list ls, V_list rs | V_tuple ls, V_tuple rs ->
        eqs lc op (Ok true) ls rs

    | V_constr ((ml, tl, cl), ls), V_constr ((mr, tr, cr), rs) ->
        if   ml != mr || tl != tr
        then Error (Type_error (op, 2, vtype_of l, vtype_of r))
        else if cl != cr
        then Ok false
        else eqs lc op (Ok true) ls rs
    | V_record l, V_record r ->
        (* Before comparing, normalize by sorting the fields. *)
        let srt m =
          List.sort (fun (fl, _) (fr, _) -> compare fl fr) m in
        let sl, sr = srt l, srt r in
        eqr lc op (Ok true) sl sr

    | V_view {vu_id = l; _}, V_view {vu_id = r; _} ->
        (* only compare their ids *)
        Ok (l = r)

    | V_set [], V_set [] | V_map [], V_map [] ->
        Ok true
    | V_set ls, V_set rs ->
        (* Before comparing, normalize by sorting the lists. *)
        eqs lc op (Ok true) (List.sort compare ls) (List.sort compare rs)

    | V_map ls, V_map rs ->
        (* Before comparing, normalize by sorting the keys. *)
        let srt m =
          List.sort (fun (kl, _) (kr, _) -> compare kl kr) m in
        let sls, srs = srt ls, srt rs in
        eqm lc op (Ok true) sls srs
    | _, _  ->
        Error (Type_error (op, 2, vtype_of l, vtype_of r))

and eqs lc op acc ls rs =
  (* we don't short circuit to catch type errors, though this won't
     catch type errors if lengths are different *)
  match ls, rs with
    | [], [] -> acc
    | hl :: tl, hr :: tr -> eqs lc op (mand acc (eq lc op hl hr)) tl tr
    | _, _ -> Ok false
and eqm lc op acc lm rm =
  (* we don't short circuit to catch type errors, though this won't
     catch type errors if lengths are different *)
  match lm, rm with
    | [], [] ->
        acc
    | (lk, lv) :: tl, (rk, rv) :: tr ->
        eqm lc op (mand (mand acc (eq lc op lk rk)) (eq lc op lv rv)) tl tr
    | _, _ ->
        Ok false
and eqr lc op acc lr rr =
  match lr, rr with
    | [], [] ->
        acc
    | (lf, lv) :: tl, (rf, rv) :: tr ->
        if   lf = rf
        then eqr lc op (mand acc (eq lc op lv rv)) tl tr
        else Ok false
    | _, _ ->
        Ok false

let equals lc (l: value) (r: value) : value =
  match eq lc "=" l r with
    | Ok b    -> V_bool b
    | Error e -> internal_error lc e

let not_equals lc (l: value) (r: value) : value =
  match eq lc "!=" l r with
    | Ok b    -> V_bool (not b)
    | Error e -> internal_error lc e

let lookup_field lc (l: value) (f: string) : value option =
  match l with
    | V_record fs ->
        List.assoc_opt f fs
    | _ ->
        internal_error lc (Type_error ("." ^ f, 1, vtype_of l, T_record [f, T_empty]))

let get_field lc (l: value) (f: string) : value =
  match l with
    | V_record fs ->
        (match List.assoc_opt f fs with
           | Some v -> v
           | None   -> internal_error lc (No_field f))
    | V_bitfield (bf, v) ->
        let hi, lo =
          match List.assoc_opt f bf.bf_fields with
            | Some r -> r
            | None   -> internal_error lc (No_field f) in
        V_bitvector (bit_extract lc v hi lo)
    | _ ->
        internal_error lc (Type_error ("." ^ f, 1, vtype_of l, T_record [f, T_empty]))

let set_field lc (l: value) (f: string) (v: value) : value =
  match l with
    | V_record fs ->
        (* The field might not be present since this might be the
           initializing assignment. *)
        (match List.assoc_opt f fs with
           | Some _ ->
               V_record (List.map (fun (f', v') ->
                             f', if f' = f then v else v'
                           ) fs)
           | None ->
               V_record ((f,v) :: fs))
    | _ ->
        internal_error lc (Type_error ("." ^ f, 1, vtype_of l, T_record [f, T_empty]))

let constr_match lc (l: value) (c: constr) : value =
  match l with
    | V_constr (c', _) ->
        V_bool (c = c')
    | _ ->
        internal_error lc (Type_error ("~~", 1, vtype_of l, T_adt_constr (c, [])))

(* subterm extraction *)
let subterm lc (v: value) (o: Ir.Anf.occurrence) : value =
  let rec walk v so =
    match v, so with
      | _, [] ->
          v
      (* native representations *)
      | V_option (Some v'), 1 :: tl ->
          walk v' tl
      | V_list (v' :: _), 1 :: tl ->
          walk v' tl
      | V_list (_ :: v'), 2 :: tl ->
          walk (V_list v') tl
      | V_tuple vs, idx :: tl ->
          let  arity = List.length vs in
          if   1 <= idx && idx <= arity
          then let v' = List.nth vs (idx - 1) in
               walk v' tl
          else let tc  = Ir.Anf.M_stdlib, "*", "_Tuple" in
               let err = Bad_subterm_index (tc, idx, o) in
               internal_error lc err
      (* user-defined constructions *)
      | V_constr (tc, args), idx :: tl ->
          let  arity = List.length args in
          if   1 <= idx && idx <= arity
          then let v' = List.nth args (idx - 1) in
               walk v' tl
          else let err = Bad_subterm_index (tc, idx, o) in
               internal_error lc err
      | _, _ ->
           let err = Bad_subterm_path (so, o) in
           internal_error lc err in
  walk v o
