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

open Values
open Runtime_exceptions

(* builtin operators *)

let int_uminus lc (v: value) : value =
  match v with
    | V_int i -> V_int (Int64.neg i)
    | _ -> fault (Type_error (lc, "uminus", 1, vtype_of v, T_int))

let bool_not lc (v: value) : value =
  match v with
    | V_bool b -> V_bool (not b)
    | _ -> fault (Type_error (lc, "not", 1, vtype_of v, T_bool))

let int_plus lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_int (Int64.add l r)
    | V_int _, _       -> fault (Type_error (lc, "+", 2, vtype_of r, T_int))
    | _, _             -> fault (Type_error (lc, "+", 1, vtype_of l, T_int))

let int_minus lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_int (Int64.sub l r)
    | V_int _, _       -> fault (Type_error (lc, "-", 2, vtype_of r, T_int))
    | _, _             -> fault (Type_error (lc, "-", 1, vtype_of l, T_int))

let int_mul lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_int (Int64.mul l r)
    | V_int _, _       -> fault (Type_error (lc, "*", 2, vtype_of r, T_int))
    | _, _             -> fault (Type_error (lc, "*", 1, vtype_of l, T_int))

let int_mod lc (l: value) (r: value) : value =
  match l, r with
    | V_int _, V_int r when r = Int64.zero -> fault (Division_by_zero lc)
    | V_int l, V_int r -> V_int (Int64.rem l r)
    | V_int _, _       -> fault (Type_error (lc, "/", 2, vtype_of r, T_int))
    | _, _             -> fault (Type_error (lc, "/", 1, vtype_of l, T_int))

let int_div lc (l: value) (r: value) : value =
  match l, r with
    | V_int _, V_int r when r = Int64.zero -> fault (Division_by_zero lc)
    | V_int l, V_int r -> V_int (Int64.div l r)
    | V_int _, _       -> fault (Type_error (lc, "/", 2, vtype_of r, T_int))
    | _, _             -> fault (Type_error (lc, "/", 1, vtype_of l, T_int))

let less_than lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_bool (Int64.compare l r < 0)
    | V_int _, _       -> fault (Type_error (lc, "<", 2, vtype_of r, T_int))
    | _, _             -> fault (Type_error (lc, "<", 1, vtype_of l, T_int))

let greater_than lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_bool (Int64.compare l r > 0)
    | V_int _, _       -> fault (Type_error (lc, ">", 2, vtype_of r, T_int))
    | _, _             -> fault (Type_error (lc, ">", 1, vtype_of l, T_int))

let le_than lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_bool (Int64.compare l r <= 0)
    | V_int _, _       -> fault (Type_error (lc, "<=", 2, vtype_of r, T_int))
    | _, _             -> fault (Type_error (lc, "<=", 1, vtype_of l, T_int))

let ge_than lc (l: value) (r: value) : value =
  match l, r with
    | V_int l, V_int r -> V_bool (Int64.compare l r >= 0)
    | V_int _, _       -> fault (Type_error (lc, ">=", 2, vtype_of r, T_int))
    | _, _             -> fault (Type_error (lc, ">=", 1, vtype_of l, T_int))

let bool_and lc (l: value) (r: value) : value =
  match l, r with
    | V_bool l, V_bool r -> V_bool (l && r)
    | V_bool _, _        -> fault (Type_error (lc, "&&", 2, vtype_of r, T_bool))
    | _, _               -> fault (Type_error (lc, "&&", 1, vtype_of l, T_bool))

let bool_or lc (l: value) (r: value) : value =
  match l, r with
    | V_bool l, V_bool r -> V_bool (l || r)
    | V_bool _, _        -> fault (Type_error (lc, "||", 2, vtype_of r, T_bool))
    | _, _               -> fault (Type_error (lc, "||", 1, vtype_of l, T_bool))

let bv_not lc (v: value) : value =
  match v with
    | V_bitvector bv -> V_bitvector (List.map not bv)
    | _              -> fault (Type_error (lc, "~", 1, vtype_of v, T_bitvector))

let bv_or lc (l: value) (r: value) : value =
  match l, r with
    | V_bitvector l, V_bitvector r when List.length l != List.length r ->
        fault (Length_mismatch (lc, "|_b", List.length l, List.length r))
    | V_bitvector l, V_bitvector r -> V_bitvector (List.map2 (||) l r)
    | V_bitvector _, _             -> fault (Type_error (lc, "|_b", 2, vtype_of r, T_bitvector))
    | _, _                         -> fault (Type_error (lc, "|_b", 1, vtype_of l, T_bitvector))

let bv_and lc (l: value) (r: value) : value =
  match l, r with
    | V_bitvector l, V_bitvector r when List.length l != List.length r ->
        fault (Length_mismatch (lc, "&_b", List.length l, List.length r))
    | V_bitvector l, V_bitvector r -> V_bitvector (List.map2 (&&) l r)
    | V_bitvector _, _             -> fault (Type_error (lc, "&_b", 2, vtype_of r, T_bitvector))
    | _, _                         -> fault (Type_error (lc, "&_b", 1, vtype_of l, T_bitvector))

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
        then fault (Type_error (lc, op, 2, vtype_of l, vtype_of r))
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
        fault (Type_error (lc, op, 2, vtype_of l, vtype_of r))

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

let list_index lc (l: value) (i: value) : value =
  match l, i with
    | V_list ls, V_int i ->
        let len = List.length ls in
        (* FIXME: this conversion is lossy on 32-bit platforms and
           hence a source of bugs.  This should be addressed via a
           resource bound mechanism, that ensures that list sizes
           don't exceed platform-specific representable bounds.
           Indices should be compared against these bounds before
           conversion. *)
        let i = Int64.to_int i in
        if 0 <= i && i < len
        then List.nth ls i
        else fault (Index_error (lc, i, len))
    | V_list _, _ ->
        fault (Type_error (lc, "[]", 2, vtype_of i, T_int))
    | _, _ ->
        fault (Type_error (lc, "[]", 1, vtype_of l, T_list T_empty))
