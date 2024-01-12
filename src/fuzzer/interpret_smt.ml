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
open Anfcfg_interpreter
open Values
open State
(* open Dispatch *)
open Parsleylib
(* open Viewlib *)
open Runtime_exceptions

exception NOT_IMPLEMENTED;;

let mod_value = AstUtils.str_of_mod

let val_of_lit (l: Ast.primitive_literal) : Smt_cfg.SMTValue.value =
  match l with
    | Ast.PL_int (i, n)  -> V_int (n, Int64.of_int i)
    | Ast.PL_bytes s     -> V_list (List.of_seq (Seq.map (fun c -> Smt_cfg.SMTValue.V_char c) (String.to_seq s)))
    | Ast.PL_unit        -> V_unit
    | Ast.PL_bool b      -> V_bool b
    | Ast.PL_bit b       -> V_bit b
    | Ast.PL_bitvector v -> V_bitvector v

(* FIXME SAMEED Continue here modify the value to constraint and operate over constraints. *)
let rec val_of_av (s: state) (av: Anf.av) : Smt_cfg.SMTValue.value =
  match av.av with
    | Anf.AV_lit l ->
        let _ = print_endline "anf.AV_lit" in
        Smt_cfg.SMTValue.V_value (val_of_lit l, "AV_lit")
    | Anf.AV_var v ->
        let _ = print_endline "AV_var" in
        let inner_value = match SMTCEnv.lookup s.st_smtcenv v av.av_loc with
            | Smt_cfg.SMTNode.N_value inner_val -> inner_val
            | Smt_cfg.SMTNode.N_record _ -> print_endline "record"; V_unit
            | Smt_cfg.SMTNode.N_unit -> print_endline "unit"; V_unit
            | Smt_cfg.SMTNode.N_call_nonterm_constraint _ -> print_endline "unit"; V_unit
            | Smt_cfg.SMTNode.N_cond_branch_constraint _ -> print_endline "unit"; V_unit
            | Smt_cfg.SMTNode.N_constraint_jump_constraint _ -> print_endline "unit"; V_unit
            | Smt_cfg.SMTNode.N_dfa_constraint _ -> print_endline "DFA"; V_unit
            | Smt_cfg.SMTNode.N_scan_constraint _ -> print_endline "unit"; V_unit
            | Smt_cfg.SMTNode.N_bits_constraint _ -> print_endline "N_bits_constraint!!"; V_unit
            | _ -> raise NOT_IMPLEMENTED
        in inner_value
    (* TODO: handle module lookup *)
    | Anf.AV_constr ((_, "*", c), avs) ->
        let _ = print_endline "AV_constr" in
        assert (c = "_Tuple");
        (* let vs = List.map (val_of_av s) avs in *)
        let vs =  List.map (val_of_av s) avs in
        Smt_cfg.SMTValue.V_value (V_tuple vs, "AV_tuple")
    | Anf.AV_constr ((_, "[]", "[]"), avs) ->
        let _ = print_endline "AV_constr" in
        assert (List.length avs = 0);
        Smt_cfg.SMTValue.V_value (V_list [], "AV_list")
    | Anf.AV_constr ((_, "[]", "::"), avs) ->
        assert (List.length avs = 2);
        let _ = print_endline "AV_constr" in
        let h  = val_of_av s (List.nth avs 0) in
        let tl = val_of_av s (List.nth avs 1) in
        let xs = List.cons h [tl] in
        Smt_cfg.SMTValue.V_value (V_list xs, "AV_constr")
    | Anf.AV_constr ((_, "option", "None"), avs) ->
        assert (List.length avs = 0);
        let v = Smt_cfg.SMTValue.V_option None in
        Smt_cfg.SMTValue.V_value (v, "AV_constr_none")
    | Anf.AV_constr ((_, "option", "Some"), avs) ->
        assert (List.length avs = 1);
        let v = val_of_av s (List.hd avs) in
        Smt_cfg.SMTValue.V_value (V_option (Some v), "AV_constr_some")
    | Anf.AV_constr ((_, "bool", "True"), avs) ->
        assert (List.length avs = 0);
        Smt_cfg.SMTValue.V_value (V_bool true, "AV_bool_true")
    | Anf.AV_constr ((_, "bool", "False"), avs) ->
        assert (List.length avs = 0);
        Smt_cfg.SMTValue.V_value (V_bool false, "AV_bool_false")
    | Anf.AV_constr ((_, "bit", "One"), avs) ->
        assert (List.length avs = 0);
        Smt_cfg.SMTValue.V_value (V_bit true, "AV_bit_true")
    | Anf.AV_constr ((_, "bit", "Zero"), avs) ->
        assert (List.length avs = 0);
        Smt_cfg.SMTValue.V_value (V_bit false, "AV_bit_false")
    | Anf.AV_constr (c, avs) ->
        Smt_cfg.SMTValue.V_value (V_constr (c, List.map (val_of_av s) avs), "AV_V_constr")
    | Anf.AV_record fs ->
        let vs = List.map (fun (f, av) ->
                     Location.value f, val_of_av s av
                   ) fs in
        Smt_cfg.SMTValue.V_value (V_record vs, "AV_V_record")
    | Anf.AV_mod_member (_m, _c) ->
            raise NOT_IMPLEMENTED
(*
        let _ = print_endline "AV_mod_member" in
        let m, c = Location.value m, Location.value c in
        if      m = "View"
        then    dispatch_viewlib av.av_loc m c s []
        else if is_lib_mod m
        then    dispatch_lib  av.av_loc m c []
        else    MVEnv.lookup s.st_mvenv (m, c) av.av_loc
*)

(* match helper, used for aexps and astmts *)

let stdlib = Anf.M_stdlib

let matcher loc vr (vl: value) cases =
  let rec do_cases cases =
    match vl, cases with
      | _, [] ->
          let err = Internal_errors.Pattern_match_failure vr in
          internal_error loc err
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

let rec val_of_aexp (s: state) (ae: Anf.aexp) : Smt_cfg.SMTValue.value =
  let do_apply s fn (ps, vs) bd loc =
    let nps, nvs = List.length ps, List.length vs in
    if   nps != nvs
    then let err = Internal_errors.Function_arity (fn, nps, nvs) in
         internal_error loc err
    else let env = List.fold_left (fun env (p, v) ->
                       SMTCEnv.assign env p v
                     ) s.st_smtcenv (List.combine ps vs) in
         val_of_aexp {s with st_smtcenv = env} bd in
  let _loc = ae.aexp_loc in
  match ae.aexp with
    | AE_val av ->
        let _ = print_endline "val_of_aexp:AE_val" in
        val_of_av s av
    | AE_unop (_op, _ae') ->
        let _ = print_endline "val_of_aexp:AE_unop" in
            raise NOT_IMPLEMENTED;
(*
        let v = val_of_av s ae' in
        (match op with
           | Uminus t -> Builtins.int_uminus t loc v
           | Inot t   -> Builtins.int_not t loc v
           | Not      -> Builtins.bool_not loc v
           | Neg_b    -> Builtins.bitvector_negate loc v)
*)
    | AE_binop (_op, _ae', _ae'') ->
        let _ = print_endline "val_of_aexp:AE_binop" in
        raise NOT_IMPLEMENTED
(*
        let v'  = val_of_av s ae' in
        let v'' = val_of_av s ae'' in
        let bin = match op with
            | Lt t    -> Builtins.less_than t
            | Gt t    -> Builtins.greater_than t
            | Lteq t  -> Builtins.le_than t
            | Gteq t  -> Builtins.ge_than t
            | Eq      -> Builtins.equals
            | Neq     -> Builtins.not_equals
            | Plus t  -> Builtins.int_plus t
            | Minus t -> Builtins.int_minus t
            | Mult t  -> Builtins.int_mul t
            | Mod t   -> Builtins.int_mod t
            | Div t   -> Builtins.int_div t
            | Iand t  -> Builtins.int_and t
            | Ior t   -> Builtins.int_or t
            | Ixor t  -> Builtins.int_xor t
            | Lshft t -> Builtins.int_lshft t
            | Rshft t -> Builtins.int_rshft t
            | Ashft t -> Builtins.int_ashft t
            | Land    -> Builtins.bool_and
            | Lor     -> Builtins.bool_or
            | Or_b    -> Builtins.bv_or
            | And_b   -> Builtins.bv_and
            | Plus_s  -> PString.concat
            | At      -> PList.concat
            | Cons    -> PList.cons
            | Index   -> PList.index in
        bin loc v' v''
*)
    | AE_bits_of_rec (_, _r, _av, _bfi) ->
        let _ = print_endline "val_of_aexp:AE_bits_of_rec" in
        raise NOT_IMPLEMENTED
(*
        Builtins.bits_of_rec loc (Location.value r) (val_of_av s av) bfi
*)
    | AE_rec_of_bits (_, _r, _av, _bfi) ->
        let _ = print_endline "val_of_aexp:AE_rec_of_bits" in
        raise NOT_IMPLEMENTED
(*
        Builtins.rec_of_bits loc (Location.value r) (val_of_av s av) bfi
*)
    | AE_bitrange (_av, _hi, _lo) ->
        let _ = print_endline "val_of_aexp:AE_bitrange" in
        raise NOT_IMPLEMENTED
(*
        Builtins.bv_bitrange loc (val_of_av s av) hi lo
*)
    | AE_match (_av, _c) ->
        let _ = print_endline "val_of_aexp:AE_match" in
        raise NOT_IMPLEMENTED
(*
        let v = val_of_av s av in
        Builtins.constr_match loc v c
*)
    | AE_field (_av, _f) ->
        let _ = print_endline "val_of_aexp:AE_field" in
        raise NOT_IMPLEMENTED
(*
        let v = val_of_av s av in
        Builtins.get_field (Location.loc f) v (Location.value f)
*)
    | AE_let (v, le, bd) ->
        let _ = print_endline "val_of_aexp:AE_let" in
        let lv = val_of_aexp s le in
        let env = SMTCEnv.assign s.st_smtcenv v (Smt_cfg.SMTNode.N_value lv) in
        val_of_aexp {s with st_smtcenv = env} bd
    | AE_cast (av, _) ->
        let _ = print_endline "val_of_aexp:AE_cast" in
        val_of_av s av
    | AE_apply (({fv = FV_var v; _} as f), args) ->
        let _ = print_endline "val_of_aexp:AE_apply FV_var" in
        let vs = List.map (val_of_av s) args in
        let node_list = List.map (fun x -> Smt_cfg.SMTNode.N_value x) vs in
        let ps, bd = FEnv.lookup s.st_fenv v f.fv_loc in
        let fn = Anf_printer.string_of_var v in
        do_apply s fn (ps, node_list) bd f.fv_loc
    | AE_apply (({fv = FV_mod_member (_m, _f); _} as _fv), _args) ->
        let _ = print_endline "val_of_aexp:AE_apply FV_mod_member" in
        raise NOT_IMPLEMENTED
(*
        let fn = Location.value f in
        let vs = List.map (val_of_av s) args in
        let mn = Location.value m in
        if      mn = "View"
        then    dispatch_viewlib fv.fv_loc mn fn s vs
        else if is_lib_mod mn
        then    dispatch_lib fv.fv_loc mn fn   vs
        else    let ps, bd = MFEnv.lookup s.st_mfenv (mn, fn) fv.fv_loc in
                do_apply s fn (ps, vs) bd fv.fv_loc
*)
    | AE_letpat (_p, (_av, _occ), _bd) ->
        let _ = print_endline "val_of_aexp:AE_letpat" in
        raise NOT_IMPLEMENTED
(*
        let v = val_of_av s av in
        let v = Builtins.subterm av.av_loc v occ in
        let env = SMTCEnv.assign s.st_smtcenv p v in
        val_of_aexp {s with st_smtcenv = env} bd
*)
    | AE_case (_vr, _cases) ->
        let _ = print_endline "val_of_aexp:AE_case" in
        raise NOT_IMPLEMENTED
(*
        let vl = SMTCEnv.lookup s.st_smtcenv vr.v vr.v_loc in
        val_of_aexp s (matcher loc vr vl cases)
*)

let rec eval_stmt (s: state) (st: Anf.astmt) : state =
  let loc = st.astmt_loc in
  match st.astmt with
    | AS_set_var (v, ae) ->
        let _ = print_endline "AS_setvar" in
        let vl = val_of_aexp s ae in
        let env = SMTCEnv.assign s.st_smtcenv v (Smt_cfg.SMTNode.N_value vl) in
        {s with st_smtcenv = env}
    | AS_set_field (r, fs, ae) ->
        let _ = print_endline "AS_set_field" in
        let fvl = Smt_cfg.SMTNode.N_value (val_of_aexp s ae) in
        (* `r` might not be bound since this might be the initializing
           assignment. *)
        let rvl = if   SMTCEnv.bound s.st_smtcenv r.v
                  then SMTCEnv.lookup s.st_smtcenv r.v loc
                  else Smt_cfg.SMTNode.N_record [] in
        (* Create records as needed for initializing assignments of
           fields of nested records. *)
        let rec set_fields rvl fs =
          match fs with
            | []      -> let err = Internal_errors.No_field_specified in
                         internal_error loc err
            | [f]     -> let lc = Location.loc f in
                         let f  = Location.value f in
                         Builtins_smt.set_field lc rvl f fvl
            | f :: fs -> let lc = Location.loc f in
                         let f  = Location.value f in
                         let rvl' =
                           match Builtins_smt.lookup_field lc rvl f with
                             | None   -> Smt_cfg.SMTNode.N_unit
                             | Some r -> r in
                         let fvl' = set_fields rvl' fs in
                         Builtins_smt.set_field lc rvl f fvl' in
        let rvl = set_fields rvl fs in
        let env = SMTCEnv.assign s.st_smtcenv r rvl in
        {s with st_smtcenv = env}
    | AS_let (v, ae, st') ->
        let _ = print_endline "AS_let" in
        let vl = val_of_aexp s ae in
        let vl' = Smt_cfg.SMTNode.N_value vl in
        let env = SMTCEnv.assign s.st_smtcenv v vl' in
        eval_stmt {s with st_smtcenv = env} st'
    | AS_case (_vr, _cases) ->
        let _ = print_endline "AS_case" in
        raise NOT_IMPLEMENTED
(*
        let vl = SMTCEnv.lookup s.st_smtcenv vr.v vr.v_loc in
        eval_stmt s (matcher loc vr vl cases)
*)
    | AS_block sts ->
        let _ = print_endline "AS_block" in
        List.fold_left eval_stmt s sts
    | AS_letpat (p, (av, occ), st') ->
        let _ = print_endline "AS_letpat" in
        let v = val_of_av s av in
        let v = Builtins_smt.subterm av.av_loc v occ in
        let nv = Smt_cfg.SMTNode.N_value v in
        let env = SMTCEnv.assign s.st_smtcenv p nv in
        eval_stmt {s with st_smtcenv = env} st'
    | AS_print (_as_ascii, _av) ->
        let _ = print_endline "AS_print" in
        raise NOT_IMPLEMENTED
(*
        let v = val_of_av s av in
        let svl = string_of_value as_ascii v in
        let svr = match av.av with
            | Anf.AV_var v -> Some (Anf_printer.string_of_var v)
            | _            -> None in
        Printf.eprintf "%s = %s\n%!"
          (match svr with
             | Some s -> s  (* print var *)
             | None   -> Location.str_of_file_loc loc)
          svl;
        s
*)
