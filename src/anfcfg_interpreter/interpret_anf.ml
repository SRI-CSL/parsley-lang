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
open Anfcfg
open Interpreter_common
open Values
open State
open Dispatch
open Parsleylib
open Viewlib

let mod_value = AstUtils.str_of_mod

let rec val_of_av (s: state) (av: Anf.av) : value =
  match av.av with
    | Anf.AV_lit l ->
        val_of_lit l
    | Anf.AV_var v ->
        VEnv.lookup s.st_venv v av.av_loc
    (* TODO: handle module lookup *)
    | Anf.AV_constr ((_, "*", c), avs) ->
        assert (c = "_Tuple");
        let vs = safe_map (val_of_av s) avs in
        V_tuple vs
    | Anf.AV_constr ((_, "[]", "[]"), avs) ->
        assert (List.length avs = 0);
        V_list []
    | Anf.AV_constr ((_, "[]", "::"), avs) ->
        assert (List.length avs = 2);
        let h  = val_of_av s (List.nth avs 0) in
        let tl = val_of_av s (List.nth avs 1) in
        PList.cons av.av_loc h tl
    | Anf.AV_constr ((_, "option", "None"), avs) ->
        assert (List.length avs = 0);
        V_option None
    | Anf.AV_constr ((_, "option", "Some"), avs) ->
        assert (List.length avs = 1);
        let v = val_of_av s (List.hd avs) in
        V_option (Some v)
    | Anf.AV_constr ((_, "bool", "True"), avs) ->
        assert (List.length avs = 0);
        V_bool true
    | Anf.AV_constr ((_, "bool", "False"), avs) ->
        assert (List.length avs = 0);
        V_bool false
    | Anf.AV_constr ((_, "bit", "One"), avs) ->
        assert (List.length avs = 0);
        V_bit true
    | Anf.AV_constr ((_, "bit", "Zero"), avs) ->
        assert (List.length avs = 0);
        V_bit false
    | Anf.AV_constr (c, avs) ->
        V_constr (c, safe_map (val_of_av s) avs)
    | Anf.AV_record fs ->
        let vs = safe_map (fun (f, av) ->
                     Location.value f, val_of_av s av
                   ) fs in
        V_record vs
    | Anf.AV_mod_member (m, c) ->
        let m, c = Location.value m, Location.value c in
        if      m = "View"
        then    dispatch_viewlib av.av_loc m c s.st_cur_view []
        else if is_lib_mod m
        then    dispatch_lib  av.av_loc m c []
        else    MVEnv.lookup s.st_mvenv (m, c) av.av_loc

(* match helper, used for aexps and astmts *)

let stdlib = Anf_common.M_stdlib

let matcher loc vr vl cases =
  let rec do_cases cases =
    match vl, cases with
      | _, [] ->
          let err = Interpreter_errors.Pattern_match_failure vr in
          Interpreter_errors.interpret_error loc err
      (* wildcard *)
      | _, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_wildcard ->
          br
      (* literals *)
      | V_int (t, i), (p, br) :: _
           when let ilit  = Int64.to_int i in
                Anf.(p.apat) = Anf.AP_literal (Ast.PL_int (ilit, t)) ->
          br
      | V_list _, (Anf.({apat = AP_literal (Ast.PL_bytes s);_}), br)
                   :: rest ->
          (match PString.try_to_string vl with
             | Some s' when s' = s -> br
             | _                   -> do_cases rest)
      | V_unit, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_literal Ast.PL_unit ->
          br
      | V_bool b, (p,br) :: _
           when Anf.(p.apat) = Anf.AP_literal (Ast.PL_bool b) ->
          br
      | V_bit b, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_literal (Ast.PL_bit b) ->
          br
      | V_bitvector bv, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_literal (Ast.PL_bitvector bv) ->
          br
      (* std constructed types with native representation *)
      | V_tuple _, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant (stdlib, "*", "_Tuple") ->
          br
      | V_list [], (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant (stdlib, "[]", "[]") ->
          br
      | V_list (_::_), (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant (stdlib, "[]", "::") ->
          br
      | V_option None, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant (stdlib, "option", "None") ->
          br
      | V_option (Some _), (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant (stdlib, "option", "Some") ->
          br
      | V_bool true, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant (stdlib, "bool", "True") ->
          br
      | V_bool false, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant (stdlib, "bool", "False") ->
          br
      | V_bit true, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant (stdlib, "bit", "One") ->
          br
      | V_bit false, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant (stdlib, "bit", "Zero") ->
          br
      (* endian and user constructed types *)
      | V_constr (c, _),  (Anf.({apat = AP_variant c'; _}), br) :: _
           when c = c' ->
          br
      | _, _ :: rest ->
          do_cases rest in
  do_cases cases

let rec val_of_aexp (s: state) (ae: Anf.aexp) : value =
  let do_apply s fn (ps, vs) bd loc =
    let nps, nvs = List.length ps, List.length vs in
    if   nps != nvs
    then let err = Interpreter_errors.Function_arity (fn, nps, nvs) in
         Interpreter_errors.interpret_error loc err
    else let env = List.fold_left (fun env (p, v) ->
                       VEnv.assign env p v
                     ) s.st_venv (List.combine ps vs) in
         val_of_aexp {s with st_venv = env} bd in
  let loc = ae.aexp_loc in
  match ae.aexp with
    | AE_val av ->
        val_of_av s av
    | AE_unop (op, ae') ->
        let v = val_of_av s ae' in
        apply_unop op v loc
    | AE_binop (op, ae', ae'') ->
        let v'  = val_of_av s ae' in
        let v'' = val_of_av s ae'' in
        apply_binop op v' v'' loc
    | AE_bits_of_rec (_, r, av, bfi) ->
        Builtins.bits_of_rec loc (Location.value r) (val_of_av s av) bfi
    | AE_rec_of_bits (_, r, av, bfi) ->
        Builtins.rec_of_bits loc (Location.value r) (val_of_av s av) bfi
    | AE_bitrange (av, hi, lo) ->
        Builtins.bv_bitrange loc (val_of_av s av) hi lo
    | AE_match (av, c) ->
        let v = val_of_av s av in
        Builtins.constr_match loc v c
    | AE_field (av, f) ->
        let v = val_of_av s av in
        Builtins.get_field (Location.loc f) v (Location.value f)
    | AE_let (v, le, bd) ->
        let lv = val_of_aexp s le in
        let env = VEnv.assign s.st_venv v lv in
        val_of_aexp {s with st_venv = env} bd
    | AE_cast (av, _) ->
        val_of_av s av
    | AE_apply (({fv = FV_var v; _} as f), args) ->
        let vs = safe_map (val_of_av s) args in
        let ps, bd = FEnv.lookup s.st_fenv v f.fv_loc in
        let fn = Anf_common.string_of_var v in
        do_apply s fn (ps, vs) bd f.fv_loc
    | AE_apply (({fv = FV_mod_member (m, f); _} as fv), args) ->
        let fn = Location.value f in
        let vs = safe_map (val_of_av s) args in
        let mn = Location.value m in
        if      mn = "View"
        then    dispatch_viewlib fv.fv_loc mn fn s.st_cur_view vs
        else if is_lib_mod mn
        then    dispatch_lib fv.fv_loc mn fn   vs
        else    let ps, bd = MFEnv.lookup s.st_mfenv (mn, fn) fv.fv_loc in
                do_apply s fn (ps, vs) bd fv.fv_loc
    | AE_letpat (p, (av, occ), bd) ->
        let v = val_of_av s av in
        let v = Builtins.subterm av.av_loc v occ in
        let env = VEnv.assign s.st_venv p v in
        val_of_aexp {s with st_venv = env} bd
    | AE_case (vr, cases) ->
        let vl = VEnv.lookup s.st_venv vr.v vr.v_loc in
        val_of_aexp s (matcher loc vr vl cases)
    | AE_print (as_ascii, ae') ->
        let v   = val_of_av s ae' in
        let svl = string_of_value as_ascii v in
        let svr = match ae'.av with
            | Anf.AV_var v -> Some (Anf_common.string_of_var v)
            | _            -> None in
        Printf.eprintf "%s = %s @ %s\n%!"
          (match svr with
             | Some s -> s  (* print var *)
             | None   -> Location.str_of_file_loc loc)
          svl
          (fmt_pos (view_info s));
        V_unit

let rec eval_stmt (s: state) (st: Anf.astmt) : state =
  let loc = st.astmt_loc in
  match st.astmt with
    | AS_set_var (v, ae) ->
        let vl = val_of_aexp s ae in
        let env = VEnv.assign s.st_venv v vl in
        {s with st_venv = env}
    | AS_set_field (r, fs, ae) ->
        let fvl = val_of_aexp s ae in
        (* `r` might not be bound since this might be the initializing
           assignment. *)
        let rvl = if   VEnv.bound s.st_venv r.v
                  then VEnv.lookup s.st_venv r.v loc
                  else V_record [] in
        (* Create records as needed for initializing assignments of
           fields of nested records. *)
        let rec set_fields rvl fs =
          match fs with
            | []      -> let err = Interpreter_errors.No_field_specified in
                         Interpreter_errors.interpret_error loc err
            | [f]     -> let lc = Location.loc f in
                         let f  = Location.value f in
                         Builtins.set_field lc rvl f fvl
            | f :: fs -> let lc = Location.loc f in
                         let f  = Location.value f in
                         let rvl' =
                           match Builtins.lookup_field lc rvl f with
                             | None   -> Values.empty_record
                             | Some r -> r in
                         let fvl' = set_fields rvl' fs in
                         Builtins.set_field lc rvl f fvl' in
        let rvl = set_fields rvl fs in
        let env = VEnv.assign s.st_venv r rvl in
        {s with st_venv = env}
    | AS_let (v, ae, st') ->
        let vl = val_of_aexp s ae in
        let env = VEnv.assign s.st_venv v vl in
        eval_stmt {s with st_venv = env} st'
    | AS_case (vr, cases) ->
        let vl = VEnv.lookup s.st_venv vr.v vr.v_loc in
        eval_stmt s (matcher loc vr vl cases)
    | AS_block sts ->
        List.fold_left eval_stmt s sts
    | AS_letpat (p, (av, occ), st') ->
        let v = val_of_av s av in
        let v = Builtins.subterm av.av_loc v occ in
        let env = VEnv.assign s.st_venv p v in
        eval_stmt {s with st_venv = env} st'
    | AS_print (as_ascii, av) ->
        let v   = val_of_av s av in
        let svl = string_of_value as_ascii v in
        let svr = match av.av with
            | Anf.AV_var v -> Some (Anf_common.string_of_var v)
            | _            -> None in
        Printf.eprintf "%s = %s @ %s\n%!"
          (match svr with
             | Some s -> s  (* print var *)
             | None   -> Location.str_of_file_loc loc)
          svl
          (fmt_pos (view_info s));
        s
