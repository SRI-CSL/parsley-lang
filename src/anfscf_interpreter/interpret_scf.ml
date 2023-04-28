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
open Scf
open Interpreter_common
open State_common
open Values
open State
open Anf_context
open Scf_context
open Parsleygram
open Internal_errors
open Runtime_exceptions

open Interpret_anf
open Interpret_bitops

(* Executions of linear or non-control flow nodes return an
   updated state. *)

let bs_wrap (f: bitstate -> bitstate) (s: state) : state =
  from_bitstate s (f (to_bitstate s))

let bs_collect_bits loc s =
  let bs = to_bitstate s in
  let bits, bs = collect_bits loc bs in
  bits, from_bitstate s bs

type elem_instr =
  | IE_next
  | IE_instr of bivalent_instr

let decompose_block (sb: sealed_block) (root: zscf)
    : elem_instr * zscf =
  let b = unseal_block sb in
  match b with
    | [] ->
        IE_next, root
    | h :: t ->
        let bz = [h], t in
        let zscf = Zscf_block (bz, root) in
        IE_instr h, zscf

(* SCF stepper state. *)

type call_info =
  Anf_common.modul * Ast.ident * (Ast.ident * value) list
  * (*return*) Anf.var * Location.t

(* Use a leading 'C' in constructors to indicate 'control', and avoid
   conflict with other constructors. *)
type scf_step_state =
  | CSS_next  of state * zscf * Location.t
  | CSS_jump  of state * next * Location.t
  | CSS_val   of state * zscf * value * Location.t
  | CSS_exp   of state * zscf * exp_step_state
  | CSS_stmt  of state * zscf * stmt_step_state
  | CSS_call  of state * zscf * call_info
  | CSS_pause of state * zscf * pause_reason * Location.t

let trace = true

let scf_step_val (s: state) (v: value) (z: zscf) : scf_step_state =
  (* There's only one possible continuation that consumes a value. *)
  match z with
    | Zscf_assign_var (vr, z) ->
        (if   trace
         then Printf.printf " %s <- [] in context %s\n"
                (Anf_printer.string_of_var vr) (str_of_top_zscf z));
        let st_venv = VEnv.assign s.st_venv vr v in
        CSS_next ({s with st_venv}, z, vr.v_loc)
    | _ ->
        assert false

(** Instruction steppers. **)

let scf_step_linear (s: state) (li: linear_instr) (z: zscf)
    : scf_step_state =
  (if   trace
   then Printf.printf " %s in context %s\n"
          (Scf_printer.str_of_linst li)
          (str_of_top_zscf z));
  let loc = li.li_loc in
  match li.li with
    (* TODO: split assignments into two kinds: one done during
       startup, which may not be worth single-stepping through, and
       the other during parsing, which are worth it. *)
    | L_assign (v, ae) ->
        let eroot = Zexp_root ae in
        let est = ESS_aexp (s, ae, eroot) in
        let z = Zscf_assign_var (v, z) in
        CSS_exp (s, z, est)

    (* Function and constant assignments are executed during
       initialization, as opposed to when processing data.  It doesn't
       seem there is much point stepping through this, so make it a
       single-step. *)
    | L_assign_fun (fv, pvs, bd, _) ->
        let st_fenv = FEnv.assign s.st_fenv fv pvs bd in
        CSS_next ({s with st_fenv}, z, loc)
    | L_assign_mod_var (m, v, ae) ->
        let vl = val_of_aexp s ae in
        let m, v = Location.value m, Location.value v in
        let st_mvenv = MVEnv.assign s.st_mvenv (m, v) vl loc in
        CSS_next ({s with st_mvenv}, z, loc)
    | L_assign_mod_fun (m, f, pvs, bd, _) ->
        let m, f = Location.value m, Location.value f in
        let st_mfenv = MFEnv.assign s.st_mfenv (m, f) pvs bd loc in
        CSS_next ({s with st_mfenv}, z, loc)

    | L_action stm ->
        let root = Zstmt_root stm in
        let sts = decompose_stmt s stm root in
        CSS_stmt (s, z, sts)

    (* Bit-matching instructions. *)

    | L_enter_bitmode ->
        CSS_next (bs_wrap (enter_bitmode loc) s, z, loc)
    | L_exit_bitmode ->
        CSS_next (bs_wrap (exit_bitmode loc) s, z, loc)
    | L_fail_bitmode ->
        CSS_next (bs_wrap (fail_bitmode loc) s, z, loc)
    | L_mark_bit_cursor ->
        CSS_next (bs_wrap (mark_bit_cursor loc) s, z, loc)

    | L_collect_bits (v, pred, obfi) ->
        let bits, s = bs_collect_bits loc s in
        if   match_bits_bound bits pred
        then let vl = match obfi with
                 | None    -> V_bitvector bits
                 | Some bf -> V_bitfield (bf, bits) in
             let env = VEnv.assign s.st_venv v vl in
             CSS_next ({s with st_venv = env}, z, loc)
        else let m = Scf_printer.string_of_mbb pred in
             let err = Interpreter_errors.Bitsbound_check m in
             Interpreter_errors.interpret_error loc err

    (* View-manipulation instructions. *)

    | L_push_view ->
        let st_view_stk = s.st_cur_view :: s.st_view_stk in
        CSS_next ({s with st_view_stk}, z, loc)
    | L_pop_view | L_drop_view
         when s.st_view_stk = [] ->
        let err = Interpreter_errors.View_stack_underflow in
        Interpreter_errors.interpret_error loc err
    | L_pop_view ->
        let vu, stk = List.hd s.st_view_stk, List.tl s.st_view_stk in
        let s = {s with st_cur_view = vu;
                        st_view_stk = stk} in
        CSS_next (s, z, loc)
    | L_drop_view ->
        let stk = List.tl s.st_view_stk in
        CSS_next ({s with st_view_stk = stk}, z, loc)
    | L_set_view v ->
        let vl = val_of_av s v in
        let s = set_view loc s vl in
        CSS_next (s, z, loc)
    | L_set_pos v ->
        let ps = val_of_av s v in
        let s = set_pos loc s ps in
        CSS_next (s, z, loc)

    | L_continue_choice ->
        assert (in_handler_block z);
        assert (last_in_block z);
        let s = restore_choice s in
        let z = continue_choice loc z in
        CSS_next (s, z, loc)

    | L_finish_choice ->
        assert (last_in_block z);
        let s = pop_choice_frame s in
        let z = finish_choice loc z in
        CSS_next (s, z, loc)

    | L_fail_choice ->
        assert (in_handler_block z);
        assert (last_in_block z);
        let s = restore_choice s in
        let s = pop_choice_frame s in
        let cont = fail_choice loc z in
        CSS_jump (s, cont, loc)

let rec scf_step_bivalent (s: state) (bi: bivalent_instr) (z: zscf)
        : scf_step_state =
  (if   trace
   then (match bi.bi with
           (* avoid double printing instructions that have their own
              printer. *)
           | B_linear _
           | B_control _ -> ()
           | _           -> Printf.printf " %s in context %s\n"
                              (Scf_printer.str_of_binst bi)
                              (str_of_top_zscf z)));
  let loc = bi.bi_loc in
  match bi.bi with
    | B_linear li ->
        scf_step_linear s li z
    | B_control ci ->
        scf_step_control s ci z

    | B_fail ->
        let cont = fail loc z in
        CSS_jump (s, cont, loc)
    | B_break ->
        let z = break loc z in
        CSS_next (s, z, loc)

    | B_bits w ->
        let bs = to_bitstate s in
        (match match_bits loc (Printf.sprintf "bits<%d>" w) bs w with
           | Ok bs    -> CSS_next (from_bitstate s bs, z, loc)
           | Error bs -> let cont = fail loc z in
                         CSS_jump (from_bitstate s bs, cont, loc))
    | B_align w ->
        let bs = to_bitstate s in
        (match align_bits loc (Printf.sprintf "align<%d>" w) bs w with
           | Ok bs    -> CSS_next (from_bitstate s bs, z, loc)
           | Error bs -> let cont = fail loc z in
                         CSS_jump (from_bitstate s bs, cont, loc))
    | B_pad w ->
        let bs = to_bitstate s in
        (match align_bits loc (Printf.sprintf "pad<%d>" w) bs w with
           | Ok bs    -> CSS_next (from_bitstate s bs, z, loc)
           | Error bs -> let cont = fail loc z in
                         CSS_jump (from_bitstate s bs, cont, loc))

    | B_collect_checked_bits (v, (mbb, pat)) ->
        let bits, s = bs_collect_bits loc s in
        if   not (match_bits_bound bits mbb)
        then let m = Scf_printer.string_of_mbb mbb in
             let err = Interpreter_errors.Bitsbound_check m in
             Interpreter_errors.interpret_error loc err
        else if match_padding bits pat
        then let bits = safe_map (fun b -> V_bool b) bits in
             let env  = VEnv.assign s.st_venv v (V_list bits) in
             CSS_next ({s with st_venv = env}, z, loc)
        else let cont = fail loc z in
             CSS_jump (s, cont, loc)
    | B_check_bits (mbb, pat) ->
        let bits, s = bs_collect_bits loc s in
        if   not (match_bits_bound bits mbb)
        then let m   = Scf_printer.string_of_mbb mbb in
             let err = Interpreter_errors.Bitsbound_check m in
             Interpreter_errors.interpret_error loc err
        else if match_padding bits pat
        then CSS_next (s, z, loc)
        else let cont = fail loc z in
             CSS_jump (s, cont, loc)

    | B_constraint av ->
        assert (s.st_mode = Mode_normal);
        if   Parsleylib.cond loc (val_of_av s av)
        then CSS_next (s, z, loc)
        else let cont = fail loc z in
             CSS_jump (s, cont, loc)

    | B_exec_dfa (dfa, v) ->
        assert (s.st_mode = Mode_normal);
        (* extend view before parsing *)
        extend_view s.st_cur_view;
        let loc = Dfa.Automaton.DFA.loc dfa in
        (match Interpret_dfa.run dfa s.st_cur_view with
           | None ->
               (* no match *)
               let cont = fail loc z in
               CSS_jump (s, cont, loc)
           | Some (vl, vu) ->
               (* matched value with updated view *)
               let env = VEnv.assign s.st_venv v vl in
               let s = {s with st_venv     = env;
                               st_cur_view = vu} in
               CSS_next (s, z, loc))

    | B_scan ((tag, dir), v) ->
        assert (s.st_mode = Mode_normal);
        (* extend view before parsing *)
        extend_view s.st_cur_view;
        let tag = Location.value tag in
        (match Interpret_dfa.scan s.st_cur_view tag dir with
           | None ->
               (* tag not found *)
               let cont = fail loc z in
               CSS_jump (s, cont, loc)
           | Some (vl, vu) ->
               (* matched value with updated view *)
               let venv = VEnv.assign s.st_venv v vl in
               let s = {s with st_venv     = venv;
                               st_cur_view = vu} in
               CSS_next (s, z, loc))

    | B_call_nonterm (m, nt, params, ret) ->
        assert (s.st_mode = Mode_normal);
        (* Extend view before parsing. *)
        extend_view s.st_cur_view;
        (* We don't have an nt_entry for stdlib non-terminals, so
           just evaluate the attribute values and dispatch. *)
        let pvs  = safe_map
                     (fun (p, av) -> p, val_of_av s av)
                     params in
        let call = m, nt, pvs, ret, loc in
        CSS_call (s, z, call)

    | B_require_remaining (v, e) ->
        let vu  = val_of_av s v in
        let vu  = Builtins.view_of v.av_loc vu in
        let req = val_of_av s e in
        let req = Builtins.int_of e.av_loc req Ast.usize_t in
        let rem = Viewlib.PView.remaining vu in
        let need = (Int64.to_int req) - rem in
        (* Extend view before bounds checks. *)
        extend_view vu;
        if   need <= 0
        then CSS_next (s, z, loc)
        else if Viewlib.PView.is_root vu
        then let pr = Paused_require_refill (vu, need) in
             CSS_pause (s, z, pr, loc)
        else fault v.av_loc (Refill_not_on_root_view need)

and scf_step_control (s: state) (ci: ctrl_instr) (z: zscf)
    : scf_step_state =
  (if   trace
   then Printf.printf " %s in context %s\n"
          (Scf_printer.str_of_cinst ci)
          (str_of_top_zscf z));
  let loc = ci.ci_loc in
  match ci.ci with
    | C_do (sb, eh) ->
        let z = Zscf_do (([], unseal_block sb), eh, z) in
        CSS_next (s, z, loc)
    | C_loop (f, sb) ->
        let z = Zscf_loop (f, ([], unseal_block sb), z) in
        CSS_next (s, z, loc)
    | C_if (av, tb, eb) ->
        if   Parsleylib.cond loc (val_of_av s av)
        then let z = Zscf_ift (av, ([], unseal_block tb), eb, z) in
             CSS_next (s, z, loc)
        else let z = Zscf_ife (av, tb, ([], unseal_block eb), z) in
             CSS_next (s, z, loc)
    | C_start_choices (fid, muts, sb) ->
        let b = unseal_block sb in
        let s = create_choice_frame s in
        let z = Zscf_start_choices (fid, muts, ([], b), z) in
        CSS_next (s, z, loc)

(* Stepper for non-terminal calls. *)

let scf_step_call (s: state) (ci: call_info) (z: zscf)
    : scf_step_state =
  match ci with
    | (m, nt, pvs, ret, loc)
         when m = Anf_common.M_stdlib
              && is_std_nonterm (Location.value nt) ->
        (if   trace
         then Printf.printf " call to %s in context %s\n"
                (Anf_common.mod_prefix m (Location.value nt))
                (str_of_top_zscf z));
        (* We don't have an nt_entry for stdlib non-terminals, so
           just evaluate the attribute values and dispatch without
           creating a call-frame. *)
        let ntn = Location.value nt in
        let pvs =
          safe_map (fun (p, vl) -> Location.value p, vl) pvs in
        (match dispatch_stdlib loc ntn s.st_cur_view pvs with
           | R_ok (vl, vu) ->
               (* An alternative would be to introduce an intermediate
                  step such as the one for `L_assign_var` and
                  transition to `CSS_val`. *)
               (* Update the environment. *)
               let env = VEnv.assign s.st_venv ret vl in
               let s'  = {s with st_venv     = env;
                                 st_cur_view = vu} in
               CSS_next (s', z, loc)
           | R_nomatch | R_err _ ->
               (* These two cases are operationally equivalent but can
                  be used for debugging. *)
               let cont = fail loc z in
               CSS_jump (s, cont, loc))
    | (m, nt, pvs, ret, loc) ->
        (if   trace
         then Printf.printf " call to %s in context %s\n"
                (Anf_common.mod_prefix m (Location.value nt))
                (str_of_top_zscf z));
        let ent = get_ntentry s (m, nt) in
        let ntn = Location.value nt in
        (* sanity check *)
        assert (ntn = Location.value ent.nt_name);
        assert (List.length pvs = Scf.StringMap.cardinal ent.nt_inh_attrs);
        (* Bind the values pointed to by params to the
           variables specified in `nt_inh_attrs`. *)
        let iattrs = ent.nt_inh_attrs in
        let env' =
          List.fold_left (fun env (p, vl) ->
              let pn = Location.value p in
              match Scf.StringMap.find_opt pn iattrs with
                | None ->
                    let err =
                      Internal_errors.Unknown_attribute (ntn, pn) in
                    internal_error (Location.loc p) err
                | Some pv ->
                    VEnv.assign env (fst pv) vl
            ) s.st_venv pvs in
        (* Set up the call frame. *)
        let cf = {cf_nt          = nt;
                  cf_nt_retvar   = ent.nt_retvar;
                  cf_choice_stk  = [];
                  cf_call_retvar = ret;
                  cf_call_cont   = z;
                  cf_call_state  = s} in
        let zcall = init_zscf ent.nt_code in
        let s' = {s with st_venv     = env';
                         st_ctrl_stk = cf :: s.st_ctrl_stk} in
        CSS_next (s', zcall, loc)

(* Stepper for returns from non-terminal calls. *)

type scf_return_result =
  | SRR_cont of state * zscf * Location.t (* continue on success *)
  | SRR_next of state * next * Location.t (* continue on failure *)
  | SRR_done of state * bool              (* done *)

let scf_step_return (s': state) (f: bool) (_l: Location.t)
    : scf_return_result =
  (if   trace
   then Printf.printf " return \n");
  match s'.st_ctrl_stk with
    | [] ->
        (* We normally cannot return to an empty stack: it should contain the
           caller's frame.  However, during startup initialization, the
           static block executes without a call frame. *)
        SRR_done (s', true)
    | cf :: stk ->
        (* Returns should be made with an empty choice stack. *)
        assert (cf.cf_choice_stk = []);
        let loc = Location.loc cf.cf_nt in
        if   f
        then
          (* This was a successful call. According to the calling
             convention, `cf_nt_retvar` should hold the matched value
             in the value environment of `s'`. *)
          let v = VEnv.lookup s'.st_venv cf.cf_nt_retvar.v loc in
          (* Update the environment of the calling state `s`. *)
          let s   = cf.cf_call_state in
          let env = VEnv.assign s.st_venv cf.cf_call_retvar v in
          (* Also update the view and pop the call frame. *)
          let s   = {s with st_venv     = env;
                            st_ctrl_stk = stk;
                            st_cur_view = s'.st_cur_view} in
          (* If the return is from the very first call, then the
             caller is the top-level and the execution is done. *)
          if   stk = []
          then SRR_done (s, true)
          else (* Resume in the caller's continuation. *)
            let z  = cf.cf_call_cont in
            SRR_cont (s, z, loc)
        else
          (* The call failed; resume with the caller's state in the
             failure handler in the caller's continuation. *)
          let s = cf.cf_call_state in
          if   stk = []
          then SRR_done (s, false)
          else let next = fail loc cf.cf_call_cont in
               SRR_next (s, next, loc)

(** The top level stepper for SCF. **)

type scf_step_result =
  | CSR_done  of state * bool
  | CSR_next  of scf_step_state
  | CSR_pause of state * zscf * pause_reason * Location.t

let step_next (s: state) (next: next) (l: Location.t)
    : scf_step_result =
  let wrap_return r =
    match r with
      | SRR_cont (s, z, l) -> CSR_next (CSS_next (s, z, l))
      | SRR_next (s, n, l) -> CSR_next (CSS_jump (s, n, l))
      | SRR_done (s, b)    -> CSR_done (s, b) in
  match next with
    | N_done_success ->
        wrap_return (scf_step_return s true l)
    | N_done_failure ->
        wrap_return (scf_step_return s false l)
    | N_in_block (bi, z) ->
        CSR_next (scf_step_bivalent s bi z)
    | N_in_handler (li, z) ->
        CSR_next (scf_step_linear s li z)

let scf_take_step (css: scf_step_state) : scf_step_result =
  match css with
    | CSS_val (s, z, v, _) ->
        CSR_next (scf_step_val s v z)
    | CSS_exp (s, z, es) ->
        (match exp_take_step es with
           | ESR_done (v, l)  -> CSR_next (CSS_val (s, z, v, l))
           | ESR_next es      -> CSR_next (CSS_exp (s, z, es)))
    | CSS_stmt (s, z, ss) ->
        (match stmt_take_step ss with
           | SSR_done (s', l) -> CSR_next (CSS_next (s', z, l))
           | SSR_next ss      -> CSR_next (CSS_stmt (s, z, ss)))
    | CSS_call (s, z, ci) ->
        CSR_next (scf_step_call s ci z)
    | CSS_jump (s, next, l) ->
        step_next s next l
    | CSS_next (s, z, l) ->
        step_next s (next l z) l
    | CSS_pause (s, z, pr, l) ->
        CSR_pause (s, z, pr, l)

(** Top level big-step executors of SCF. **)

type scf_result =
  | CR_done  of state * bool
  | CR_pause of state * zscf * pause_reason * Location.t

let run_scf (s: state) (sb: sealed_block) (l: Location.t)
    : scf_result =
  let rec stepper st =
    match scf_take_step st with
      | CSR_done (s, b)         -> CR_done (s, b)
      | CSR_next st             -> stepper st
      | CSR_pause (s, z, pr, l) -> CR_pause (s, z, pr, l) in
  let zinit = init_zscf sb in
  let st = CSS_next (s, zinit, l) in
  stepper st

let run_cont (s: state) (z: zscf) (l: Location.t)
    : scf_result =
  let rec stepper st =
    match scf_take_step st with
      | CSR_done (s, b)         -> CR_done (s, b)
      | CSR_next st             -> stepper st
      | CSR_pause (s, z, pr, l) -> CR_pause (s, z, pr, l) in
  let st = CSS_next (s, z, l) in
  stepper st
