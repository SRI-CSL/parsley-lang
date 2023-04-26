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
open Anfscf
open Interpreter_common
open Values
open State
open Anf_context
open Dispatch
open Parsleylib
open Viewlib

(** Utilities for expression steppers. **)

let mod_value = AstUtils.str_of_mod

let val_of_lit (l: Ast.primitive_literal) : value =
  match l with
    | Ast.PL_int (i, n)  -> V_int (n, Int64.of_int i)
    | Ast.PL_bytes s     -> PString.to_byte_list s
    | Ast.PL_unit        -> V_unit
    | Ast.PL_bool b      -> V_bool b
    | Ast.PL_bit b       -> V_bit b
    | Ast.PL_bitvector v -> V_bitvector v

let stdlib = Anf_common.M_stdlib

let apply_unop (op: Ast.unop) v loc =
  match op with
    | Uminus t -> Builtins.int_uminus t loc v
    | Inot t   -> Builtins.int_not t loc v
    | Not      -> Builtins.bool_not loc v
    | Neg_b    -> Builtins.bitvector_negate loc v

let apply_binop (op: Ast.binop) vl vr loc =
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
  bin loc vl vr

let print_val loc s (as_ascii: bool) (av: Anf.av) (v: value) =
  let svl = string_of_value as_ascii v in
  let svr = match av.av with
      | Anf.AV_var v -> Some (Anf_common.string_of_var v)
      | _            -> None in
  Printf.eprintf "%s = %s @ %s\n%!"
    (match svr with
       | Some s -> s  (* print var *)
       | None   -> Location.str_of_file_loc loc)
    svl
    (fmt_pos (view_info s))

(** Basic expression stepper: av -> value **)

let rec val_of_av (s: state) (av: Anf.av) : value =
  match av.av with
    | Anf.AV_lit l ->
        val_of_lit l
    | Anf.AV_var v ->
        VEnv.lookup s.st_venv v av.av_loc
    | Anf.AV_constr ((m, "*", c), avs) ->
        assert (m = stdlib);
        assert (c = "_Tuple");
        let vs = safe_map (val_of_av s) avs in
        V_tuple vs
    | Anf.AV_constr ((m, "[]", "[]"), avs) ->
        assert (m = stdlib);
        assert (List.length avs = 0);
        V_list []
    | Anf.AV_constr ((m, "[]", "::"), avs) ->
        assert (m = M_stdlib);
        assert (List.length avs = 2);
        let h  = val_of_av s (List.nth avs 0) in
        let tl = val_of_av s (List.nth avs 1) in
        PList.cons av.av_loc h tl
    | Anf.AV_constr ((m, "option", "None"), avs) ->
        assert (m = stdlib);
        assert (List.length avs = 0);
        V_option None
    | Anf.AV_constr ((m, "option", "Some"), avs) ->
        assert (m = stdlib);
        assert (List.length avs = 1);
        let v = val_of_av s (List.hd avs) in
        V_option (Some v)
    | Anf.AV_constr ((m, "bool", "True"), avs) ->
        assert (m = stdlib);
        assert (List.length avs = 0);
        V_bool true
    | Anf.AV_constr ((m, "bool", "False"), avs) ->
        assert (m = stdlib);
        assert (List.length avs = 0);
        V_bool false
    | Anf.AV_constr ((m, "bit", "One"), avs) ->
        assert (m = stdlib);
        assert (List.length avs = 0);
        V_bit true
    | Anf.AV_constr ((m, "bit", "Zero"), avs) ->
        assert (m = stdlib);
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

(* Though expression evaluation has no side-effects in the object
   language, it does extend the environment and hence modify the
   interpreter state in the meta language.

   A design choice made here is to thread the interpreter state
   through the stepper, since it seems simpler.  However, lexical
   scoping for `let` bound variables needs to be maintained: when the
   locus of execution leaves a variable scope, that variable should be
   removed from the value environment.

   This is implemented by tracking the introduced variables in the
   frames in the zipper context.  When the zipper is reduced past
   these frames (specifically, _let and _letpat), the variables are
   removed.  This is implemented by inserting an appropriately placed
   `drop_var` frame. *)

(* The most elementary expression to evaluate is either an Anf.av or
   an external or a function call. *)
type elem_exp =
  | E_av of Anf.av
  | E_call of Anf.fv * value list * Location.t

(* The states in the step-transition graph. *)
type exp_step_state =
  | ESS_val of state * value * Location.t * zexp
  | ESS_aexp of state * Anf.aexp * zexp
  | ESS_call of state * Anf.fv * value list * Location.t * zexp
  | ESS_done of value * Location.t

let loc_of_exp_state st : Location.t =
  match st with
    | ESS_val (_, _, l, _)
    | ESS_call (_, _, _, l, _)
    | ESS_done (_, l) -> l
    | ESS_aexp (_, ae, _) -> ae.aexp_loc

(** Compute the stepper state for an expression by decomposing it into
    an elementary expression and its continuation. **)
let decompose_aexp (s: state) (ae: Anf.aexp) (root: zexp) : exp_step_state =
  let rec setup ae z =
    let si = Anf.(ae.aexp_site) in
    let loc = Anf.(ae.aexp_loc) in
    match Anf.(ae.aexp) with
      | AE_val av ->
          ESS_val (s, val_of_av s av, av.av_loc, z)
      | AE_apply (f, []) ->
          ESS_call (s, f, [], ae.aexp_loc, z)
      | AE_apply (f, (av :: _ as avs)) ->
          let z = Zexp_apply (f, [], avs, loc, si, z) in
          ESS_val (s, val_of_av s av, av.av_loc, z)
      | AE_unop (op, av) ->
          let z = Zexp_unop (op, loc, si, z) in
          ESS_val (s, val_of_av s av, av.av_loc, z)
      | AE_binop (op, avl, avr) ->
          let z = Zexp_binop1 (op, avl, avr, loc, si, z) in
          ESS_val (s, val_of_av s avl, avl.av_loc, z)
      | AE_bits_of_rec (av, info) ->
          let z = Zexp_bits_of_rec (info, loc, si, z) in
          ESS_val (s, val_of_av s av, av.av_loc, z)
      | AE_rec_of_bits (av, info) ->
          let z = Zexp_rec_of_bits (info, loc, si, z) in
          ESS_val (s, val_of_av s av, av.av_loc, z)
      | AE_bitrange (av, h, l) ->
          let z = Zexp_bitrange (h, l, loc, si, z) in
          ESS_val (s, val_of_av s av, av.av_loc, z)
      | AE_match (av, c) ->
          let z = Zexp_match (c, loc, si, z) in
          ESS_val (s, val_of_av s av, av.av_loc, z)
      | AE_field (av, f) ->
          let z = Zexp_field (f, loc, si, z) in
          ESS_val (s, val_of_av s av, av.av_loc, z)
      | AE_case (av, cases) ->
          let z = Zexp_cases (av, cases, si, z) in
          ESS_val (s, val_of_av s av, av.av_loc, z)
      | AE_let (v, bind, bod) ->
          let zdrop = Zexp_drop_var (v, si, z) in
          setup bind (Zexp_let (v, bod, si, zdrop))
      | AE_cast (av, t) ->
          let z = Zexp_cast (t, loc, si, z) in
          ESS_val (s, val_of_av s av, av.av_loc, z)
      | AE_print (f, av) ->
          let z = Zexp_print (f, av, loc, si, z) in
          ESS_val (s, val_of_av s av, av.av_loc, z)
      | AE_letpat (v, (av, occ), body) ->
          let zdrop = Zexp_drop_var (v, si, z) in
          let z = Zexp_letpat (occ, v, body, si, zdrop) in
          ESS_val (s, val_of_av s av, av.av_loc, z)
  in setup ae root

(** A function call stepper returns either a value (from an external
   function) or the body expression and an updated evaluation state
   and continuation. **)
let exp_step_call (s: state) (z: zexp) (fv: Anf.fv) (vs: value list)
      loc : exp_step_state =
  let setup_eval fn ps bd loc =
    let nps, nvs = List.length ps, List.length vs in
    if   nps != nvs
    then let err = Interpreter_errors.Function_arity (fn, nps, nvs) in
         Interpreter_errors.interpret_error loc err
    else let env = List.fold_left (fun env (p, v) ->
                       VEnv.assign env p v
                     ) s.st_venv (List.combine ps vs) in
         ESS_aexp ({s with st_venv = env}, bd, z) in
  match fv.fv with
    | FV_var v ->
        let ps, bd = FEnv.lookup s.st_fenv v fv.fv_loc in
        let fn = Anf_common.string_of_var v in
        setup_eval fn ps bd fv.fv_loc
    | FV_mod_member (m, f) ->
        let mn, fn = Location.value m, Location.value f in
        if   mn = "View"
        then let v = dispatch_viewlib fv.fv_loc mn fn s.st_cur_view vs in
             ESS_val (s, v, loc, z)
        else if is_lib_mod mn
        then let v = dispatch_lib fv.fv_loc mn fn vs in
             ESS_val (s, v, loc, z)
        else let ps, bd = MFEnv.lookup s.st_mfenv (mn, fn) fv.fv_loc in
             setup_eval fn ps bd fv.fv_loc

(* When returning a value in `step_val`, a site is attached from the
   `zexp` context only when the context is reduced to its tail. For
   eg., the site is only attached when a binary operation is fully
   reduced.  When a context is reduced but an `aexp` is returned,
   there are two possible sites: the one in aexp and the one in the
   original context `zexp`.  In this case, we pick one using
   `pick_site`. *)
let pick_site sil sir =
  (* left-biased site picker *)
  match sil with
    | Some _ -> sil
    | None   -> sir

(** A value stepper is given a computed value and takes a step into
   the continuation. **)
let exp_step_val (s: state) (v: value) (loc: Location.t) (z: zexp)
    : exp_step_state =
  match z with
    | Zexp_root _ ->
        ESS_done (v, loc)
    | Zexp_apply (_, _, [], _, _, _) ->
        (* There should be an arg which we just evaluated. *)
        assert false
    | Zexp_apply (fv, vals, [av], loc, _si, z) ->
        let _, vs = List.split (List.rev ((av, v) :: vals)) in
        ESS_call (s, fv, vs, loc, z)
    | Zexp_apply (fv, vs, av :: (av' :: _ as avs), loc, si, z) ->
        let vs = (av, v) :: vs in
        let v = val_of_av s av' in
        let z = Zexp_apply (fv, vs, avs, loc, si, z) in
        ESS_val (s, v, av'.av_loc, z)
    | Zexp_unop (op, loc, _si, z) ->
        let v = apply_unop op v loc in
        ESS_val (s, v, loc, z)
    | Zexp_binop1 (op, avl, avr, loc, si, z) ->
        let vr = val_of_av s avr in
        let z  = Zexp_binop2 (op, (avl, v), avr, loc, si, z) in
        ESS_val (s, vr, avr.av_loc, z)
    | Zexp_binop2 (op, (_, vl), _, loc, _si, z) ->
        let v = apply_binop op vl v loc in
        ESS_val (s, v, loc, z)
    | Zexp_bits_of_rec ((_, r, bfi), loc, _si, z) ->
        let v = Builtins.bits_of_rec loc (Location.value r) v bfi in
        ESS_val (s, v, loc, z)
    | Zexp_rec_of_bits ((_, r, bfi), loc, _si, z) ->
        let v = Builtins.rec_of_bits loc (Location.value r) v bfi in
        ESS_val (s, v, loc, z)
    | Zexp_bitrange (h, l, loc, _si, z) ->
        let v = Builtins.bv_bitrange loc v h l in
        ESS_val (s, v, loc, z)
    | Zexp_match (c, loc, _si, z) ->
        let v = Builtins.constr_match loc v c in
        ESS_val (s, v, loc, z)
    | Zexp_field (f, loc, _si, z) ->
        let v = Builtins.get_field (Location.loc f) v (Location.value f) in
        ESS_val (s, v, loc, z)
    | Zexp_cases (av, cases, si, z) ->
        let ae = matcher loc av v cases in
        (* We are losing `si` and may not have one in `ae`. Pick one. *)
        let si = pick_site si ae.aexp_site in
        let ae = {ae with aexp_site = si} in
        ESS_aexp (s, ae, z)
    | Zexp_let (var, ae, si, z) ->
        let env = VEnv.assign s.st_venv var v in
        (* We are losing `si` and may not have one in `ae`. Pick one. *)
        let si = pick_site si ae.aexp_site in
        let ae = {ae with aexp_site = si} in
        let s  = {s with st_venv = env} in
        ESS_aexp (s, ae, z)
    | Zexp_cast (_, loc, _si, z) ->
        ESS_val (s, v, loc, z)
    | Zexp_print (f, av, loc, _si, z) ->
        print_val loc s f av v;
        ESS_val (s, V_unit, loc, z)
    | Zexp_letpat (occ, var, ae, si, z) ->
        let v = Builtins.subterm var.v_loc v occ in
        let env = VEnv.assign s.st_venv var v in
        (* We are losing `si` and may not have one in `ae`. Pick one. *)
        let si = pick_site si ae.aexp_site in
        let ae = {ae with aexp_site = si} in
        let s  = {s with st_venv = env} in
        ESS_aexp (s, ae, z)
    | Zexp_drop_var (vr, _si, z) ->
        let env = VEnv.remove s.st_venv vr.v in
        let s   = {s with st_venv = env} in
        ESS_val (s, v, loc, z)

(** Top-level expression stepper. **)

type exp_step_result =
  | ESR_done of value * Location.t
  | ESR_next of exp_step_state
let exp_take_step (step: exp_step_state) : exp_step_result =
  match step with
    | ESS_val (s, v, l, z) ->
        ESR_next (exp_step_val s v l z)
    | ESS_aexp (s, ae, z) ->
        ESR_next (decompose_aexp s ae z)
    | ESS_call (s, fv, vs, l, z) ->
        ESR_next (exp_step_call s z fv vs l)
    | ESS_done (v, l) ->
        ESR_done (v, l)

(** Big-step expression evaluator. **)

let val_of_aexp (s: state) (ae: Anf.aexp) : value =
  let rec stepper st =
    match exp_take_step st with
      | ESR_next st      -> stepper st
      | ESR_done (v, _)  -> v in
  let root = Zexp_root ae in
  let st = ESS_aexp (s, ae, root) in
  stepper st

(** Utilities for steppers for statement execution. **)

(* Field assignment helper for assignment statements. *)
let assign_field (s: state) (r: Anf.var) (fs: Ast.ident list) (fvl: value)
  (loc: Location.t) : state =
  (* `r` might not be bound since this might be the initializing
     assignment. *)
  let rvl = if   VEnv.bound s.st_venv r.v
            then VEnv.lookup s.st_venv r.v loc
            else V_record [] in
  (* Create records as needed for initializing assignments of fields
     of nested records. *)
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

(* The side-effects to the value environment from statement execution
   are tracked by threading the state through the step transitions.
   However, lexical scoping needs to be maintained: when the locus of
   execution leaves a variable scope, that variable should be removed
   from the value environment.

   This is implemented by tracking the introduced variables in the
   zipper context.  When the zipper is reduced past these introduction
   points (specifically, _let and _letpat), the variables are removed.
   This is implemented by inserting an appropriately placed `drop_var`
   frame. *)

(* Compute the starting stepper state for a statement, which
   specifies the first step and its continuation. *)
type elem_stmt =
  | SE_exp  of Anf.aexp
  | SE_val  of value * Location.t
  | SE_next of Location.t

let loc_of_elem e : Location.t =
  match e with
    | SE_exp ae     -> ae.aexp_loc
    | SE_val (_, l)
    | SE_next l     -> l

type stmt_step_state =
  | SSS_elem of state * elem_stmt * zstmt
  | SSS_exp of state * exp_step_state * zstmt
  | SSS_val of state * value * Location.t * zstmt
  | SSS_next of state * zstmt * Location.t
  | SSS_done of state * Location.t

let loc_of_stmt_state s : Location.t =
  match s with
    | SSS_elem (_, e, _)   -> loc_of_elem e
    | SSS_exp (_, s, _)    -> loc_of_exp_state s
    | SSS_val (_, _, l, _)
    | SSS_next (_, _, l)
    | SSS_done (_, l)      -> l

let decompose_stmt (s: state) (stm: Anf.astmt) (root: zstmt)
    : stmt_step_state =
  let rec setup stm z =
    let si = Anf.(stm.astmt_site) in
    let loc = Anf.(stm.astmt_loc) in
    match stm.astmt with
      | AS_set_var (v, ae) ->
          let e = SE_exp ae in
          let z = Zstmt_set_var (v, loc, si, z) in
          SSS_elem (s, e, z)
      | AS_set_field (r, fs, ae) ->
          let e = SE_exp ae in
          let z = Zstmt_set_field (r, fs, loc, si, z) in
          SSS_elem (s, e, z)
      | AS_print (f, av) ->
          let e = SE_val (val_of_av s av, av.av_loc) in
          let z = Zstmt_print (f, av, si, z) in
          SSS_elem (s, e, z)
      | AS_let (v, ae, stm) ->
          let zdrop = Zstmt_drop_var (v, si, z) in
          let e = SE_exp ae in
          let z = Zstmt_let (v, stm, si, zdrop) in
          SSS_elem (s, e, z)
      | AS_case (av, cases) ->
          let e = SE_val (val_of_av s av, av.av_loc) in
          let z = Zstmt_cases (av, cases, si, z) in
          SSS_elem (s, e, z)
      | AS_block [] ->
          SSS_elem (s, SE_next loc, z)
      | AS_block (h :: t) ->
          setup h (Zstmt_block (t, si, z))
      | AS_letpat (v, (av, occ), stm) ->
          let zdrop = Zstmt_drop_var (v, si, z) in
          let e = SE_val (val_of_av s av, av.av_loc) in
          let z = Zstmt_letpat (occ, v, stm, si, zdrop) in
          SSS_elem (s, e, z) in
  setup stm root

(** A value stepper takes a state expecting a value and computes an
    updated state and the next stepper state in the continuation. **)
type stmt_step_val_result = state * sinfo * zstmt
let stmt_step_val (s: state) (vl: value) (z: zstmt)
    : stmt_step_val_result =
  (* Only continuations created with a corresponding value providing
     `elem_stmt` in `decompose_stmt` expect a value. *)
  match z with
    | Zstmt_set_var (var, _l, si, z) ->
        let env = VEnv.assign s.st_venv var vl in
        {s with st_venv = env}, si, z
    | Zstmt_set_field (r, fs, loc, si, z) ->
        let s = assign_field s r fs vl loc in
        s, si, z
    | Zstmt_print (f, av, si, z) ->
        print_val av.av_loc s f av vl;
        s, si, z
    | Zstmt_let (var, stm, si, z) ->
        let env = VEnv.assign s.st_venv var vl in
        {s with st_venv = env}, si, Zstmt_stmt (stm, z)
    | Zstmt_cases (av, cases, si, z) ->
        let stm = matcher av.av_loc av vl cases in
        s, si, Zstmt_stmt (stm, z)
    | Zstmt_letpat (occ, var, stm, si, z) ->
        let vl = Builtins.subterm var.v_loc vl occ in
        let env = VEnv.assign s.st_venv var vl in
        {s with st_venv = env}, si, Zstmt_stmt (stm, z)
    (* The remaining continuations don't take a value. *)
    | Zstmt_root _
    | Zstmt_block _
    | Zstmt_stmt _
    | Zstmt_drop_var _ ->
        assert false

(** A statement stepper for states that are not expecting a computed
   value. **)
let stmt_step_unit (s: state) (z: zstmt) (l: Location.t)
    : stmt_step_state =
  match z with
    | Zstmt_root _ ->
        SSS_done (s, l)
    | Zstmt_block ([], _si, z) ->
        SSS_next (s, z, l)
    | Zstmt_block (stm :: ss, si, z) ->
        decompose_stmt s stm (Zstmt_block (ss, si, z))
    | Zstmt_stmt (stm, z) ->
        decompose_stmt s stm z
    | Zstmt_drop_var (v, _si, z) ->
        let env = VEnv.remove s.st_venv v.v in
        let s   = {s with st_venv = env} in
        SSS_next (s, z, l)
    (* The remaining continuations take a value. *)
    | Zstmt_set_var _
    | Zstmt_set_field _
    | Zstmt_print _
    | Zstmt_let _
    | Zstmt_cases _
    | Zstmt_letpat _ ->
        assert false

let stmt_step_elem (s: state) (e: elem_stmt) (zs: zstmt)
    : stmt_step_state =
  match e with
    | SE_exp ae ->
        let eroot = Zexp_root ae in
        let est = ESS_aexp (s, ae, eroot) in
        (match exp_take_step est with
           | ESR_next est ->
               SSS_exp (s, est, zs)
           | ESR_done (v, l) ->
               SSS_val (s, v, l, zs))
    | SE_val (v, l) ->
        SSS_val (s, v, l, zs)
    | SE_next l ->
        SSS_next (s, zs, l)

type stmt_step_result =
  | SSR_done of state * Location.t
  | SSR_next of stmt_step_state
let stmt_take_step (sss: stmt_step_state) =
  match sss with
    | SSS_exp (s, es, zs) ->
        (match exp_take_step es with
           | ESR_done (v, l) ->
               SSR_next (SSS_val (s, v, l, zs))
           | ESR_next es ->
               SSR_next (SSS_exp (s, es, zs)))
    | SSS_val (s, v, l, zs) ->
        let s, _si, zs = stmt_step_val s v zs in
        SSR_next (SSS_next (s, zs, l))
    | SSS_done (s, l)  ->
        SSR_done (s, l)
    | SSS_next (s, zs, l) ->
        let st = stmt_step_unit s zs l in
        SSR_next st
    | SSS_elem (s, e, zs) ->
        SSR_next (stmt_step_elem s e zs)

(** Big-step expression executor. **)

let eval_stmt (s: state) (st: Anf.astmt) : state =
  let rec stepper st =
    match stmt_take_step st with
      | SSR_next st     -> stepper st
      | SSR_done (s, _) -> s in
  let root = Zstmt_root st in
  let st = decompose_stmt s st root in
  stepper st
