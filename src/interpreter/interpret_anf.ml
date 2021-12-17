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

open Parsing
open Ir
open Values
open State
open Parsleylib
open Viewlib
open Runtime_exceptions

let val_of_lit (l: Ast.primitive_literal) : value =
  match l with
    | Ast.PL_int i       -> V_int (Int64.of_int i)
    | Ast.PL_string s    -> V_string s
    | Ast.PL_unit        -> V_unit
    | Ast.PL_bool b      -> V_bool b
    | Ast.PL_bit b       -> V_bit b
    | Ast.PL_bitvector v -> V_bitvector v

let rec val_of_av (s: state) (av: Anf.av) : value =
  match av.av with
    | Anf.AV_lit l ->
        val_of_lit l
    | Anf.AV_var v ->
        VEnv.lookup s.st_venv v av.av_loc
    | Anf.AV_constr ((t, c), avs) ->
        let t, c = Location.value t, Location.value c in
        V_constr ((t, c), List.map (val_of_av s) avs)
    | Anf.AV_record fs ->
        let vs = List.map (fun (f, av) ->
                     Location.value f, val_of_av s av
                   ) fs in
        V_record vs
    | Anf.AV_mod_member (m, c) ->
        let m, c = Location.value m, Location.value c in
        dispatch_stdlib av.av_loc m c []

let rec val_of_aexp (s: state) (ae: Anf.aexp) : value =
  let loc = ae.aexp_loc in
  match ae.aexp with
    | AE_val av ->
        val_of_av s av
    | AE_unop (op, ae') ->
        let v = val_of_av s ae' in
        (match op with
           | Uminus -> Builtins.int_uminus loc v
           | Not    -> Builtins.bool_not loc v
           | Neg_b  -> Builtins.bitvector_negate loc v)
    | AE_binop (op, ae', ae'') ->
        let v'  = val_of_av s ae' in
        let v'' = val_of_av s ae'' in
        let bin = match op with
            | Lt     -> Builtins.less_than
            | Gt     -> Builtins.greater_than
            | Lteq   -> Builtins.le_than
            | Gteq   -> Builtins.ge_than
            | Eq     -> Builtins.equals
            | Neq    -> Builtins.not_equals
            | Plus   -> Builtins.int_plus
            | Minus  -> Builtins.int_minus
            | Mult   -> Builtins.int_mul
            | Mod    -> Builtins.int_mod
            | Div    -> Builtins.int_div
            | Land   -> Builtins.bool_and
            | Lor    -> Builtins.bool_or
            | Or_b   -> Builtins.bv_or
            | And_b  -> Builtins.bv_and
            | Plus_s -> PString.concat
            | At     -> PList.concat
            | Cons   -> PList.cons
            | Index  -> PList.index in
        bin loc v' v''
    | AE_bits_of_rec (r, av, bfi) ->
        Builtins.bits_of_rec loc (Location.value r) (val_of_av s av) bfi
    | AE_rec_of_bits (r, av, bfi) ->
        Builtins.rec_of_bits loc (Location.value r) (val_of_av s av) bfi
    | AE_bitrange (av, hi, lo) ->
        Builtins.bv_bitrange loc (val_of_av s av) hi lo
    | AE_match (av, (t, c)) ->
        let v = val_of_av s av in
        Builtins.constr_match loc v (Location.value t, Location.value c)
    | AE_field (av, f) ->
        let v = val_of_av s av in
        Builtins.record_field (Location.loc f) v (Location.value f)
    | AE_let (v, le, bd) ->
        let lv = val_of_aexp s le in
        let env = VEnv.assign s.st_venv v true lv in
        val_of_aexp {s with st_venv = env} bd
    | AE_cast (av, _) ->
        val_of_av s av
    | AE_apply (({fv = FV_var v; _} as f), args) ->
        let vs = List.map (val_of_av s) args in
        let ps, bd = FEnv.lookup s.st_fenv v f.fv_loc in
        let nps, nvs = List.length ps, List.length vs in
        if   nps != nvs
        then let fn = Anf_printer.string_of_var v in
             let err = Internal_errors.Function_arity (f.fv_loc, fn, nps, nvs) in
             internal_error err
        else let env = List.fold_left (fun env (p, v) ->
                           VEnv.assign env p true v
                         ) s.st_venv (List.combine ps vs) in
             val_of_aexp {s with st_venv = env} bd
    | AE_apply (({fv = FV_mod_member (m, f); _} as fv), args) ->
        let vs = List.map (val_of_av s) args in
        let m = Location.value m in
        if   m = "View"
        then dispatch_viewlib fv.fv_loc m (Location.value f) s vs
        else dispatch_stdlib  fv.fv_loc m (Location.value f)   vs
    | AE_letpat (p, (av, occ), bd) ->
        let v = val_of_av s av in
        let v = Builtins.subterm av.av_loc v occ in
        let env = VEnv.assign s.st_venv p true v in
        val_of_aexp {s with st_venv = env} bd
    | AE_case (vr, cases) ->
        let vl = VEnv.lookup s.st_venv vr.v vr.v_loc in
        let rec matcher cases =
          match vl, cases with
            | _, [] ->
                let err = Internal_errors.Pattern_match_failure (loc, vr) in
                internal_error err
            | _, (p, ae) :: _
                 when Anf.(p.apat) = Anf.AP_wildcard ->
                ae
            | V_int i, (p, ae) :: _
                 when let ilit  = Int64.to_int i in
                      Anf.(p.apat) = Anf.AP_literal (Ast.PL_int ilit) ->
                ae
            | V_string s, (p, ae) :: _
                 when Anf.(p.apat) = Anf.AP_literal (Ast.PL_string s) ->
                ae
            | V_unit, (p, ae) :: _
                 when Anf.(p.apat) = Anf.AP_literal Ast.PL_unit ->
                ae
            | V_bool b, (p, ae) :: _
                 when Anf.(p.apat) = Anf.AP_literal (Ast.PL_bool b) ->
                ae
            | V_bit b, (p, ae) :: _
                 when Anf.(p.apat) = Anf.AP_literal (Ast.PL_bit b) ->
                ae
            | V_bitvector bv, (p, ae) :: _
                 when Anf.(p.apat) = Anf.AP_literal (Ast.PL_bitvector bv) ->
                ae
            | V_constr (c, _),  (p, ae) :: _
                 when Anf.(p.apat) = Anf.AP_variant c ->
                ae
            | _, _ :: rest ->
                matcher rest in
        val_of_aexp s (matcher cases)
