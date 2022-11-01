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
open Values
open State
open Parsleygram
open Runtime_exceptions
open Interpret_anf
open Interpret_bitops

(* Executions of linear or non-control flow nodes return an
   updated state. *)

let do_gnode (s: state) (n: Cfg.gnode) : state =
  let loc = n.node_loc in
  match n.node with
    | N_assign (vr, ae) ->
        let vl = val_of_aexp s ae in
        let st_venv = VEnv.assign s.st_venv vr vl in
        {s with st_venv}
    | N_assign_fun (fv, pvs, bd, _) ->
        let st_fenv = FEnv.assign s.st_fenv fv pvs bd in
        {s with st_fenv}
    | N_assign_mod_var (m, v, ae) ->
        let vl = val_of_aexp s ae in
        let m, v = Location.value m, Location.value v in
        let st_mvenv = MVEnv.assign s.st_mvenv (m, v) vl loc in
        {s with st_mvenv}
    | N_assign_mod_fun (m, f, pvs, bd, _) ->
        let m, f = Location.value m, Location.value f in
        let st_mfenv = MFEnv.assign s.st_mfenv (m, f) pvs bd loc in
        {s with st_mfenv}
    | N_action sts ->
        List.fold_left eval_stmt s sts
    | N_enter_bitmode ->
        enter_bitmode loc s
    | N_exit_bitmode ->
        exit_bitmode loc s
    | N_fail_bitmode ->
        fail_bitmode loc s
    | N_mark_bit_cursor ->
        mark_bit_cursor loc s
    | N_collect_bits (v, pred, obf) ->
        let bits, s = collect_bits loc s in
        if   match_bits_bound bits pred
        then let vl = match obf with
                 | None    -> V_bitvector bits
                 | Some bf -> V_bitfield (bf, bits) in
             let env = VEnv.assign s.st_venv v vl in
             {s with st_venv = env}
        else let m = Cfg_printer.string_of_mbb pred in
             let err = Internal_errors.Bitsbound_check m in
             internal_error loc err
    | N_push_view ->
        let st_view_stk = s.st_cur_view :: s.st_view_stk in
        {s with st_view_stk}
    | N_pop_view | N_drop_view
         when s.st_view_stk = [] ->
        let err = Internal_errors.View_stack_underflow in
        internal_error loc err
    | N_pop_view ->
        let vu, stk = List.hd s.st_view_stk, List.tl s.st_view_stk in
        {s with st_cur_view = vu;
                st_view_stk = stk}
    | N_drop_view ->
        let stk = List.tl s.st_view_stk in
        {s with st_view_stk = stk}
    | N_set_view v ->
        let vl = VEnv.lookup s.st_venv v.v v.v_loc in
        Viewlib.set_view loc s vl
    | N_set_pos v ->
        let ps = VEnv.lookup s.st_venv v.v v.v_loc in
        Viewlib.set_pos loc s ps

let do_entry_node (s: state) (n: Cfg.Node.entry_node)
    : state =
  match n with
    | Cfg.Node.N_label _ ->
        (* TODO: perhaps check some invariant here? *)
        s
    | _ ->
        (* this should not be needed *)
        assert false

let do_linear_node (s: state) (n: Cfg.Node.linear_node)
    : state =
  match n with
    | Cfg.Node.N_gnode nd ->
        do_gnode s nd
    | _ ->
        (* this should not be needed *)
        assert false

(* The below functions process control-flow nodes and closed blocks
   (i.e. blocks that end with a control-flow or exit node).  These
   functions tail-recurse into each other, updating the control-stack
   in the state at call/return nodes.

   The executed blocks and nodes span the CFGs of the different
   non-terminals in the grammar.  The transition (or 'call') from one
   CFG into another occurs at a `N_call_nonterm` node, while the
   transition back occurs at `N_return`.

   The nodes of a block are executed in sequence.  If its exit node
   transfers control to a static label, execution continues directly
   (and tail-recursively) to the block with that label.  Execution
   'returns to caller' when control flow reaches a virtual label via a
   `N_return` node.

   A sequence of such calls during execution results in call frames
   being built up in the control stack, as each caller non-terminal
   waits for its callee non-terminal to terminate execution.  These
   calls terminate with a `N_return` instruction, which pops a call
   frame and continues execution from the continuations specified in
   it.

   The execution ends when there is no continuation at which to
   proceed (as set in the very first call-frame); equivalently, it
   ends when the call control-stack is empty.  The return value of a
   successful execution is the value of the match, along with the
   final state (which contains the final view with its offset).  On
   failure, the last stuck state is returned for diagnostics.

   The execution can also pause or suspend with a particular
   `Cfg_paused` result, containing a `pause_reason` that can be
   handled at the top-level by an application-provided pause handler.
   The `Cfg_paused` block contains the label of the block at which the
   suspended execution can resume.  The requirement here is that the
   CFG nodes triggering the suspension, and at which the execution
   must resume, are always at the beginning of the labeled block.
 *)

type cfg_result =
  | Cfg_paused of Location.t * pause_reason * Cfg.label
  | Cfg_ok of value
  | Cfg_error of state

type parse_result = cfg_result * state

let rec do_jump lc (s: state) (l: Cfg.label) : parse_result =
  assert (Cfg.is_static l);
  let b = get_block lc s l in
  do_closed_block s b

and do_return _lc (s': state) (l: Cfg.label) : parse_result =
  assert (Cfg.is_virtual l);
  match s'.st_ctrl_stk with
    | [] ->
        (* We should have an activation frame to match the return. *)
        assert false
    | cf :: stk ->
        let loc = Location.loc cf.cf_nt in
        if   l = cf.cf_nt_succcont
        then (* According to the calling convention, `cf_nt_retvar`
                should hold the matched value in the value environment
                of `s'`. *)
             let vl = VEnv.lookup s'.st_venv cf.cf_nt_retvar.v loc in
             (* Update the environment of the calling state `s`. *)
             let s = cf.cf_call_state in
             let env = match cf.cf_call_retvar with
                 | None    -> s.st_venv
                 | Some vr -> VEnv.assign s.st_venv vr vl in
             (* Update the view and pop the control stack. *)
             let s = {s with st_venv     = env;
                             st_ctrl_stk = stk;
                             st_cur_view = s'.st_cur_view} in
             match cf.cf_conts with
               | Some (lsc, _) ->
                   (* Transfer control to the success continuation. *)
                   do_jump loc s lsc
               | None ->
                   (* Return to the top-level *)
                   assert (stk = []);
                   Cfg_ok vl, s
        else if l = cf.cf_nt_failcont
        then let s = cf.cf_call_state in
             (* The view should not be modified by the call (except
                when the  call is from the top-level). *)
             assert (stk = [] || s.st_cur_view = s'.st_cur_view);
             (* Pop the control stack. *)
             let s = {s with st_ctrl_stk = stk} in
             match cf.cf_conts with
               | Some (_, lf) ->
                   (* Transfer control to the failure continuation
                      without any change to the view. *)
                   do_jump loc s lf
               | None ->
                   (* Return to the top-level, passing the failing state. *)
                   assert (stk = []);
                   Cfg_error s', s
        else assert false (* Unrecognized label. *)

and do_exit_node (s: state) (n: Cfg.Node.exit_node) : parse_result =
  match n with
    | N_bits (loc, w, lsc, lf) ->
        (match match_bits loc (Printf.sprintf "bits<%d>" w) s w with
           | Ok s    -> do_jump loc s lsc
           | Error s -> do_jump loc s lf)
    | N_align (loc, w, lsc, lf) ->
        (match align_bits loc (Printf.sprintf "align<%d>" w) s w with
           | Ok s    -> do_jump loc s lsc
           | Error s -> do_jump loc s lf)
    | N_pad (loc, w, lsc, lf) ->
        (match align_bits loc (Printf.sprintf "pad<%d>" w) s w with
           | Ok s    -> do_jump loc s lsc
           | Error s -> do_jump loc s lf)
    | Cfg.Node.N_collect_checked_bits (loc, v, (mbb, pat), lsc, lf) ->
        let bits, s = collect_bits loc s in
        if   not (match_bits_bound bits mbb)
        then let m   = Cfg_printer.string_of_mbb mbb in
             let err = Internal_errors.Bitsbound_check m in
             internal_error loc err
        else if match_padding bits pat
        then let bits = safe_map (fun b -> V_bool b) bits in
             let env  = VEnv.assign s.st_venv v (V_list bits) in
             let s    = {s with st_venv = env} in
             do_jump loc s lsc
        else do_jump loc s lf
    | Cfg.Node.N_check_bits (loc, (mbb, pat), lsc, lf) ->
        let bits, s = collect_bits loc s in
        if   not (match_bits_bound bits mbb)
        then let m   = Cfg_printer.string_of_mbb mbb in
             let err = Internal_errors.Bitsbound_check m in
             internal_error loc err
        else if match_padding bits pat
        then do_jump loc s lsc
        else do_jump loc s lf
    | Cfg.Node.N_jump (loc, l) ->
        do_jump loc s l
    | Cfg.Node.N_return (loc, l) ->
        do_return loc s l
    | Cfg.Node.N_constraint (loc, v, lsc, lf) ->
        assert (s.st_mode = Mode_normal);
        let vl = VEnv.lookup s.st_venv v.v v.v_loc in
        if   Parsleylib.cond loc vl
        then do_jump loc s lsc
        else do_jump loc s lf
    | Cfg.Node.N_cond_branch (loc, v, lsc, lf) ->
        assert (s.st_mode = Mode_normal);
        let vl = VEnv.lookup s.st_venv v.v v.v_loc in
        let b = Parsleylib.cond v.v_loc vl in
        do_jump loc s (if b then lsc else lf)
    | Cfg.Node.N_exec_dfa (dfa, v, lsc, lf) ->
        assert (s.st_mode = Mode_normal);
        (* extend view before parsing *)
        extend_view s.st_cur_view;
        let loc = Dfa.DFA.loc dfa in
        let run = Interpret_dfa.run dfa s.st_cur_view in
        (match run with
           | None ->
               (* no match *)
               do_jump loc s lf
           | Some (vl, vu) ->
               (* matched value with updated view *)
               let env = VEnv.assign s.st_venv v vl in
               let s = {s with st_venv     = env;
                               st_cur_view = vu} in
               do_jump loc s lsc)
    | Cfg.Node.N_scan (loc, (tag, dir), v, lsc, lf) ->
        assert (s.st_mode = Mode_normal);
        (* extend view before parsing *)
        extend_view s.st_cur_view;
        let tag = Location.value tag in
        let run = Interpret_dfa.scan s.st_cur_view tag dir in
        (match run with
           | None ->
               (* tag not found *)
               do_jump loc s lf
           | Some (vl, vu) ->
               (* matched value with updated view *)
               let venv = VEnv.assign s.st_venv v vl in
               let s = {s with st_venv     = venv;
                               st_cur_view = vu} in
               do_jump loc s lsc)

    | Cfg.Node.N_call_nonterm (m, nt, params, ret, lsc, lf)
         when m = Anf.M_stdlib
              && is_std_nonterm (Location.value nt) ->
        assert (s.st_mode = Mode_normal);
        (* Extend view before parsing. *)
        extend_view s.st_cur_view;
        (* We don't have an nt_entry for stdlib non-terminals, so
           just evaluate the attribute values and dispatch. *)
        let ntn = Location.value nt in
        let loc = Location.loc nt in
        let pvs =
          safe_map (fun (p, vr) ->
              let vl = VEnv.lookup s.st_venv Anf.(vr.v) vr.v_loc in
              Location.value p, vl
            ) params in
        (* There is no assertion on the continuations since they need
           not be virtual, unlike user-defined non-terminals.  This is
           because stdlib non-terminals are not dispatched by an
           `nt_entry`, and hence do not have explicitly defined
           virtual continuation labels. *)
        (match dispatch_stdlib loc ntn s.st_cur_view pvs with
           | R_ok (vl, vu) ->
               (* Update the environment of the calling state `s`. *)
               let env = match ret with
                   | None    -> s.st_venv
                   | Some vr -> VEnv.assign s.st_venv vr vl in
               (* Transfer control to the success continuation. *)
               do_jump loc {s with st_venv = env;
                                   st_cur_view = vu} lsc
           | R_nomatch | R_err _ ->
               (* These two cases are operationally equivalent but can
                  be used for debugging. *)
               (* Transfer control to the failure continuation. *)
               do_jump loc s lf)
    | Cfg.Node.N_call_nonterm (m, nt, params, ret, lsc, lf) ->
        assert (s.st_mode = Mode_normal);
        let ent = get_ntentry s (m, nt) in
        let ntn = Location.value nt in
        (* sanity check *)
        assert (ntn = Location.value ent.nt_name);
        assert (List.length params = Cfg.StringMap.cardinal ent.nt_inh_attrs);
        (* Bind the values pointed to by params to the
           variables specified in `nt_inh_attrs`. *)
        let iattrs = ent.nt_inh_attrs in
        let env' =
          List.fold_left (fun env (p, vr) ->
              (* Looking up env or s.st_venv should be equivalent. *)
              let vl = VEnv.lookup s.st_venv Anf.(vr.v) vr.v_loc in
              let pn = Location.value p in
              match Cfg.StringMap.find_opt pn iattrs with
                | None ->
                    let err =
                      Internal_errors.Unknown_attribute (ntn, pn) in
                    internal_error (Location.loc p) err
                | Some pv ->
                    VEnv.assign env (fst pv) vl
            ) s.st_venv params in
        (* Set up the call frame. *)
        let cf = {cf_nt          = nt;
                  cf_conts       = Some (lsc, lf);
                  cf_nt_succcont = ent.nt_succcont;
                  cf_nt_failcont = ent.nt_failcont;
                  cf_nt_retvar   = ent.nt_retvar;
                  cf_call_retvar = ret;
                  cf_call_state  = s} in
        let loc = Location.loc nt in
        let b   = get_block loc s (Cfg.L_static ent.nt_entry) in
        let s'  = {s with st_venv     = env';
                          st_ctrl_stk = cf :: s.st_ctrl_stk} in
        do_closed_block s' b

    (* Suspend/resume. *)

    | Cfg.Node.N_require_remaining (v, e, lr, ln) ->
        let vu  = VEnv.lookup s.st_venv v.v v.v_loc in
        let vu  = Builtins.view_of v.v_loc vu in
        let req = VEnv.lookup s.st_venv e.v e.v_loc in
        let req = Builtins.int_of e.v_loc req Ast.usize_t in
        let rem = Viewlib.PView.remaining vu in
        let need = (Int64.to_int req) - rem in
        (* Extend view before bounds checks. *)
        extend_view vu;
        if   need <= 0
        then do_jump v.v_loc s ln
        else if Viewlib.PView.is_root vu
        then let pr = Paused_require_refill (vu, need) in
             Cfg_paused (v.v_loc, pr, lr), s
        else fault v.v_loc (Refill_not_on_root_view need)

    | _ ->
        (* this should not be needed *)
        assert false

and do_closed_block (s: state) (b: Cfg.closed) : parse_result =
  let e, b = Cfg.B.split_head b in
  let b, x = Cfg.B.split_tail b in
  let ns   = Cfg.B.to_list b in
  let s = do_entry_node s e in
  let s = List.fold_left do_linear_node s ns in
  do_exit_node s x

(* This is only called to initialize the statics, and has no parsing
   result. *)
let do_opened_block (s: state) (b: Cfg.opened) : state =
  let e, b = Cfg.B.split_head b in
  let ns   = Cfg.B.to_list b in
  let s = do_entry_node s e in
  List.fold_left do_linear_node s ns
