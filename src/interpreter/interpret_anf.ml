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
    | Ast.PL_bytes s     -> PString.to_byte_list s
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
    | Anf.AV_constr ((t, c), avs)
         when Location.value t = "*" ->
        assert (Location.value c = "_Tuple");
        let vs = List.map (val_of_av s) avs in
        V_tuple vs
    | Anf.AV_constr ((t, c), avs)
         when Location.value t = "[]" && Location.value c = "[]" ->
        assert (List.length avs = 0);
        V_list []
    | Anf.AV_constr ((t, c), avs)
         when Location.value t = "[]" && Location.value c = "::" ->
        assert (List.length avs = 2);
        let h  = val_of_av s (List.nth avs 0) in
        let tl = val_of_av s (List.nth avs 1) in
        PList.cons av.av_loc h tl
    | Anf.AV_constr ((t, c), avs)
         when Location.value t = "option" && Location.value c = "None" ->
        assert (List.length avs = 0);
        V_option None
    | Anf.AV_constr ((t, c), avs)
         when Location.value t = "option" && Location.value c = "Some" ->
        assert (List.length avs = 1);
        let v = val_of_av s (List.hd avs) in
        V_option (Some v)
    | Anf.AV_constr ((t, c), avs)
         when Location.value t = "bool" && Location.value c = "True" ->
        assert (List.length avs = 0);
        V_bool true
    | Anf.AV_constr ((t, c), avs)
         when Location.value t = "bool" && Location.value c = "False" ->
        assert (List.length avs = 0);
        V_bool false
    | Anf.AV_constr ((t, c), avs)
         when Location.value t = "bit" && Location.value c = "One" ->
        assert (List.length avs = 0);
        V_bit true
    | Anf.AV_constr ((t, c), avs)
         when Location.value t = "bit" && Location.value c = "Zero" ->
        assert (List.length avs = 0);
        V_bit false
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
        if   m = "View"
        then dispatch_viewlib av.av_loc m c s []
        else dispatch_stdlib  av.av_loc m c []

(* match helper, used for aexps and astmts *)
let matcher loc vr vl cases =
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
      | V_int i, (p, br) :: _
           when let ilit  = Int64.to_int i in
                Anf.(p.apat) = Anf.AP_literal (Ast.PL_int ilit) ->
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
           when Anf.(p.apat) = Anf.AP_variant ("*", "_Tuple") ->
          br
      | V_list [], (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant ("[]", "[]") ->
          br
      | V_list (_::_), (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant ("[]", "::") ->
          br
      | V_option None, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant ("option", "None") ->
          br
      | V_option (Some _), (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant ("option", "Some") ->
          br
      | V_bool true, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant ("bool", "True") ->
          br
      | V_bool true, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant ("bool", "False") ->
          br
      | V_bit true, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant ("bit", "One") ->
          br
      | V_bit false, (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant ("bit", "Zero") ->
          br
      (* endian and user constructed types *)
      | V_constr (c, _),  (p, br) :: _
           when Anf.(p.apat) = Anf.AP_variant c ->
          br
      | _, _ :: rest ->
          do_cases rest in
  do_cases cases

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
        Builtins.get_field (Location.loc f) v (Location.value f)
    | AE_let (v, le, bd) ->
        let lv = val_of_aexp s le in
        let env = VEnv.assign s.st_venv v lv in
        val_of_aexp {s with st_venv = env} bd
    | AE_cast (av, _) ->
        val_of_av s av
    | AE_apply (({fv = FV_var v; _} as f), args) ->
        let vs = List.map (val_of_av s) args in
        let ps, bd = FEnv.lookup s.st_fenv v f.fv_loc in
        let nps, nvs = List.length ps, List.length vs in
        if   nps != nvs
        then let fn = Anf_printer.string_of_var v in
             let err = Internal_errors.Function_arity (fn, nps, nvs) in
             internal_error f.fv_loc err
        else let env = List.fold_left (fun env (p, v) ->
                           VEnv.assign env p v
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
        let env = VEnv.assign s.st_venv p v in
        val_of_aexp {s with st_venv = env} bd
    | AE_case (vr, cases) ->
        let vl = VEnv.lookup s.st_venv vr.v vr.v_loc in
        val_of_aexp s (matcher loc vr vl cases)

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
            | []      -> let err = Internal_errors.No_field_specified in
                         internal_error loc err
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
    | AS_print av ->
        let v = val_of_av s av in
        let svl = string_of_value v in
        let svr = match av.av with
            | Anf.AV_var v -> Some (Anf_printer.string_of_var v)
            | _            -> None in
        Printf.eprintf "%s = %s\n"
          (match svr with
             | Some s -> s  (* print var *)
             | None   -> Location.str_of_file_loc loc)
          svl;
        s
