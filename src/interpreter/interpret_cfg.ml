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
open Parsleygram
open Runtime_exceptions
open Interpret_anf
open Interpret_bitops

let do_gnode (s: state) (n: Cfg.gnode) : state =
  let loc = n.node_loc in
  match n.node with
    | N_assign (vr, ae) ->
        let vl = val_of_aexp s ae in
        let st_venv = VEnv.assign s.st_venv vr vl in
        {s with st_venv}
    | N_assign_fun (fv, pvs, bd) ->
        let st_fenv = FEnv.assign s.st_fenv fv pvs bd in
        {s with st_fenv}
    | N_action sts ->
        List.fold_left eval_stmt s sts
    | N_enter_bitmode ->
        enter_bitmode loc s
    | N_exit_bitmode ->
        exit_bitmode loc s
    | N_bits w ->
        match_bits loc (Printf.sprintf "bits<%d>" w) s w
    | N_align w ->
        align_bits loc (Printf.sprintf "align<%d>" w) s w
    | N_pad w ->
        align_bits loc (Printf.sprintf "pad<%d>" w) s w
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
        else let m = Ir_printer.string_of_mbb pred in
             let err = Internal_errors.Bitsbound_check (loc, m) in
             internal_error err
    | N_push_view ->
        let st_view_stk = s.st_cur_view :: s.st_view_stk in
        {s with st_view_stk}
    | N_pop_view | N_drop_view
         when s.st_view_stk = [] ->
        let err = Internal_errors.View_stack_underflow loc in
        internal_error err
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

let do_pop_failcont lc (s: state) (l: Cfg.label) : state =
  (* pop the top-most failcont, ensure that it is the specified label,
     and return the updated state *)
  match s.st_failcont_stk with
    | [] ->
        let err = Internal_errors.Failcont_stack_underflow lc in
        internal_error err
    | le :: stk ->
        if   l != le
        then let err = Internal_errors.Unexpected_failcont (lc, l, le) in
             internal_error err
        else {s with st_failcont_stk = stk}

let do_linear_node (s: state) (n: Cfg.Node.linear_node)
    : state =
  match n with
    | Cfg.Node.N_gnode nd ->
        do_gnode s nd
    | Cfg.Node.N_push_failcont (_, l) ->
        {s with st_failcont_stk = l :: s.st_failcont_stk}
    | Cfg.Node.N_pop_failcont (loc, l) ->
        do_pop_failcont loc s l
    | _ ->
        (* this should not be needed *)
        assert false

(* A block executes its nodes in sequence.  If its exit node transfers
   control to a static label, execution continues directly (and
   tail-recursively) to the block with that label.  Execution stops
   (i.e. "returns to caller") when control flow reaches a dynamic
   label.

   Dynamic labels are used to terminate the CFG of a non-terminal, and
   hence to terminate the execution of the blocks in the
   non-terminal's CFG.

   `N_call_nonterm` (i.e. starting and ending a non-terminal parse) is
   the only node that is not processed tail-recursively; i.e. it
   maintains state on the interpreter's stack.  `N_call_nonterm` needs
   to process the result of the non-terminal parse differently
   depending on whether the parse succeeded or failed.  So it waits on
   the stack until control reaches one of its dynamic labels, i.e. the
   label for either the success or the failure continuation.
   Terminating block execution at a dynamic label allows control to
   return to `N_call_nonterm`.  The termination code indicates the
   type of termination (success or failure).

   Non-terminal production rules are in terms of other non-terminals;
   this manifests in a non-terminal CFG containing `N_call_nonterm`
   nodes to these other non-terminals.  A sequence of such calls
   during execution results in state being built up on the
   interpreter's stack, as each non-terminal waits for its "child"
   non-terminal to terminate execution. *)

type code =
  | C_success
  | C_failure

type result = code * state * Cfg.label  (* this label should always be dynamic *)

let rec do_jump lc (s: state) (l: Cfg.label) : result =
  if   Cfg.is_dynamic l
  then C_success, s, l
  else let b = get_block lc s l in
       do_closed_block s b

(* A failure to a static label should correspond to an entry at the
   top of the failcont stack, and this entry is popped before
   proceeding.  A failure to a dynamic label corresponds to a return
   to the caller. *)
and do_fail lc (s: state) (l: Cfg.label) : result =
  if   Cfg.is_dynamic l
  then C_failure, s, l
  else let s = do_pop_failcont lc s l in
       let b = get_block lc s l in
       do_closed_block s b

and do_exit_node (s: state) (n: Cfg.Node.exit_node) : result =
  match n with
    | Cfg.Node.N_collect_checked_bits (loc, v, (mbb, pat), lsc, lf) ->
        let bits, s = collect_bits loc s in
        if   not (match_bits_bound bits mbb)
        then let m   = Ir_printer.string_of_mbb mbb in
             let err = Internal_errors.Bitsbound_check (loc, m) in
             internal_error err
        else if match_padding bits pat
        then let bits = List.map (fun b -> V_bool b) bits in
             let env  = VEnv.assign s.st_venv v (V_list bits) in
             let s    = {s with st_venv = env} in
             do_jump loc s lsc
        else do_fail loc s lf
    | Cfg.Node.N_check_bits (loc, (mbb, pat), lsc, lf) ->
        let bits, s = collect_bits loc s in
        if   not (match_bits_bound bits mbb)
        then let m   = Ir_printer.string_of_mbb mbb in
             let err = Internal_errors.Bitsbound_check (loc, m) in
             internal_error err
        else if match_padding bits pat
        then do_jump loc s lsc
        else do_fail loc s lf
    | Cfg.Node.N_jump (loc, l) ->
        do_jump loc s l
    | Cfg.Node.N_constraint (loc, v, lsc, lf) ->
        let vl = VEnv.lookup s.st_venv v.v v.v_loc in
        if   Parsleylib.cond loc vl
        then do_jump loc s lsc
        else do_fail loc s lf
    | Cfg.Node.N_cond_branch (loc, v, lsc, lf) ->
        let vl = VEnv.lookup s.st_venv v.v v.v_loc in
        let b = Parsleylib.cond v.v_loc vl in
        do_jump loc s (if b then lsc else lf)
    | Cfg.Node.N_exec_dfa (dfa, v, lsc, lf) ->
        let loc = Ir.Dfa.DFA.loc dfa in
        let run = Interpret_dfa.run dfa s.st_cur_view in
        (match run with
           | None ->
               (* no match *)
               do_fail loc s lf
           | Some (vl, vu) ->
               (* matched value with updated view *)
               let env = VEnv.assign s.st_venv v vl in
               let s = {s with st_venv     = env;
                               st_cur_view = vu} in
               do_jump loc s lsc)
    | Cfg.Node.N_call_nonterm (nt, params, ret, lsc, lf)
         when is_std_nonterm (Location.value nt) ->
        (* We don't have an nt_entry for stdlib non-terminals, so
           just evaluate the attribute values and dispatch. *)
        let ntn = Location.value nt in
        let loc = Location.loc nt in
        let pvs =
          List.map (fun (p, vr) ->
              let vl = VEnv.lookup s.st_venv Anf.(vr.v) vr.v_loc in
              Location.value p, vl
            ) params in
        (* There is no assertion on the continuations since they need
           not be dynamic, unlike user-defined non-terminals.  This is
           because stdlib non-terminals are not dispatched by an
           `nt_entry`, and hence do not have explicitly defined
           dynamic continuation labels. *)
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
               (* These are operationally equivalent but can be used
                  for debugging. *)
               (* Transfer control to the failure continuation. *)
               do_fail loc s lf
        )
    | Cfg.Node.N_call_nonterm (nt, params, ret, lsc, lf) ->
        let ent = get_ntentry s nt in
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
                    let loc = Location.loc p in
                    let err =
                      Internal_errors.Unknown_attribute (loc, ntn, pn) in
                    internal_error err
                | Some pv ->
                    VEnv.assign env (fst pv) vl
            ) s.st_venv params in
        let loc = Location.loc nt in
        let b   = get_block loc s (Cfg.L_static ent.nt_entry) in
        let s' = {s with st_venv = env'} in
        (* Wait on the stack until the CFG terminates at one of its
           dynamic labels. *)
        let code, s', l = do_closed_block s' b in
        assert (Cfg.is_dynamic l);
        (match code with
           | C_success ->
               (* We should have terminated at the specified success
                  continuation. *)
               assert (l = ent.nt_succcont);
               (* According to the calling convention, `ent.retvar`
                  should hold the matched value in the value
                  environment of `s'`. *)
               let vl = VEnv.lookup s'.st_venv ent.nt_retvar.v loc in
               (* Update the environment of the calling state `s`. *)
               let env = match ret with
                   | None    -> s.st_venv
                   | Some vr -> VEnv.assign s.st_venv vr vl in
               (* Transfer control to the success continuation with
                  the updated view. *)
               do_jump loc {s with st_venv     = env;
                                   st_cur_view = s'.st_cur_view} lsc
           | C_failure ->
               (* We should have terminated at the specified failure
                  continuation. *)
               assert (l = ent.nt_failcont);
               (* Transfer control to the failure continuation without
                  any change to the view. *)
               assert (s.st_cur_view = s'.st_cur_view);
               do_fail loc s lf)
    | _ ->
        (* this should not be needed *)
        assert false

and do_closed_block (s: state) (b: Cfg.closed) : result =
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
