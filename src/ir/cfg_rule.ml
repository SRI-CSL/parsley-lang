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
open Typing
open Flow
open Anf
open Cfg

(* type and expression utilities *)

let mk_ident (n: string) l =
  Location.mk_loc_val n l

let mk_mod_member (m: string) (v: string) t l =
  let m = Location.mk_loc_val m l in
  let v = Location.mk_loc_val v l in
  make_av (AV_mod_member (m, v)) t l

let get_typ ctx name =
  let typ = Ast.TName name in
  TypingEnvironment.typcon_variable ctx.ctx_tenv typ

let mk_func_type ctx arg res =
  TypeAlgebra.arrow (TypingEnvironment.as_fun ctx.ctx_tenv)
    arg res

let get_nt_typ ctx name =
  let nt = Ast.NName name in
  match TypingEnvironment.lookup_non_term_type ctx.ctx_tenv nt with
    | Some t -> t
    | None -> assert false

let av_of_int ctx i loc =
  let int = get_typ ctx "int" in
  make_av (AV_lit (PL_int i)) int loc

let fresh_var venv typ loc =
  let vid, venv = VEnv.gen venv in
  make_var vid typ loc, venv

let bind_var venv v t =
  let v', venv = VEnv.bind venv v in
  make_var v' t (Location.loc v), venv

let constr_av t c args typ loc =
  let t = mk_ident t loc in
  let c = mk_ident c loc in
  make_av (AV_constr ((t, c), args)) typ loc

(* block manipulation utilities *)

let new_labeled_block (l: Label.label) : opened =
  let h = Node.N_label l in
  B.join_head h B.empty

let new_block () : Label.label * opened =
  let l = Label.fresh_label () in
  l, new_labeled_block l

let add_node b nd =
  B.snoc b nd

let add_gnode b nd typ loc =
  let nd = mk_gnode nd typ loc in
  add_node b (Node.N_gnode nd)

let close_with_jump ctx b l =
  let nd = Node.N_jump l in
  let b = B.join_tail b nd in
  {ctx with ctx_ir = FormatIR.add (B.entry_label b) b ctx.ctx_ir}

let close_block ctx b nd =
  let b = B.join_tail b nd in
  {ctx with ctx_ir = FormatIR.add (B.entry_label b) b ctx.ctx_ir}

(* returns the labels to use for failure continuations for a set of
   ordered choices.  each choice fails to the next one, except for the
   last choice, which fails to the provided continuation.  for
   convenience in a list folder, provide a boolean to indicate whether
   the label is the last one.  *)
let mk_choice_labels choices final_cont =
  let rec mk_fls fls cs =
    match cs with
      | [] -> fls
      | _ :: [] -> (final_cont, true) :: fls
      | _ :: t  -> mk_fls ((Label.fresh_label (), false) :: fls) t in
  List.rev (mk_fls [] choices)

(* handle inserting a mark_bit_cursor if needed for a return value *)
let prepare_cursor
      (ctx: context) (b: opened) (ret: return) (loc: Location.t)
    : opened =
  match ret with
    | None -> b
    | Some _ ->
        (* no other sensible type for mark_bit_cursor *)
        let typ = get_typ ctx "unit" in
        add_gnode b N_mark_bit_cursor typ loc

(* collect matched bits into a variable if needed *)
let collect_cursor
      (b: opened) (bnd: matched_bits_bound) (ret: return) (typ: typ)
      (loc: Location.t)
    : opened =
  match ret with
    | None -> b
    | Some (v, fresh) ->
        let nd = N_collect_bits (v, fresh, bnd) in
        add_gnode b nd typ loc

(* Note: The construction of the CFG often involves glue code in ANF.
   Ideally, this glue code would be constructed in the AST form, then
   run through the type-checker, then normalized via Anf_exp; this
   would ensure type-correctness.

   However, as currently implemented, this process loses the link
   between the ANF vars we have in the CFG and the constructed ANF,
   since fresh and unrelated ANF vars are created during Anf_exp
   normalization.  It appears that modifying Anf_exp to handle both
   cases (i.e. source AST -> ANF as well as constructed AST -> ANF)
   would make the current Anf_exp overly complicated.  It would be
   good to fix this via some restructuring. *)

let rec lower_rule_elem
          (ctx: context) (b: opened) (ret: return) (re: rule_elem)
        : (context * opened) =
  let typ = re.rule_elem_aux in
  let loc = re.rule_elem_loc in
  match re.rule_elem with
    (* bit-level support *)

    | RE_bitvector bits ->
        let b = prepare_cursor ctx b ret loc in
        let bits = Location.value bits in
        let b = add_gnode b (N_bits bits) typ loc in
        let bnd = MB_exact bits in
        let b = collect_cursor b bnd ret typ loc in
        ctx, b

    | RE_align bits ->
        let b = prepare_cursor ctx b ret loc in
        let bits = Location.value bits in
        let b = add_gnode b (N_align bits) typ loc in
        let bnd = MB_below bits in
        let b = collect_cursor b bnd ret typ loc in
        ctx, b

    | RE_pad (bits, pat) ->
        let b = prepare_cursor ctx b ret loc in
        let bits = Location.value bits in
        let b = add_gnode b (N_pad (bits, pat)) typ loc in
        let bnd = MB_below bits in
        let b = collect_cursor b bnd ret typ loc in
        ctx, b

    | RE_bitfield bf ->
        (* This is equivalent to RE_bits for the underlying number of
           bits.  The interpretation of the matched value as a
           bitfield record is done by the record accessors. *)
        let bits =
          TypedAstUtils.lookup_bitfield_length ctx.ctx_tenv bf in
        let b = prepare_cursor ctx b ret loc in
        let b = add_gnode b (N_bits bits) typ loc in
        let bnd = MB_exact bits in
        let b = collect_cursor b bnd ret typ loc in
        ctx, b

    (* other basic primitives *)

    | RE_regexp r ->
        (* Compile the regexp into a DFA. *)
        let dfa = Cfg_regexp.build_dfa ctx.ctx_re_env r in
        (* Bind a new var for the matched value if we don't have a
           return binding. *)
        let v, venv =
          match ret with
            | None -> fresh_var ctx.ctx_venv typ loc
            | Some (v', _) -> v', ctx.ctx_venv in
        (* The call to execute the DFA closes the current block, and
           the success continuation begins in a new block (with the
           same rationale as for RE_non_term). *)
        let lsc = Label.fresh_label () in
        let nd = Node.N_exec_dfa (dfa, v, lsc, ctx.ctx_failcont) in
        let ctx = close_block {ctx with ctx_venv = venv} b nd in
        ctx, new_labeled_block lsc

    | RE_seq_flat _ ->
        assert (TypedAstUtils.is_regexp_elem ctx.ctx_tenv re);
        let rx = TypedAstUtils.to_regexp re in
        (* Now do as above *)
        (* Compile the regexp into a DFA. *)
        let dfa = Cfg_regexp.build_dfa ctx.ctx_re_env rx in
        (* Bind a new var for the matched value if we don't have a
           return binding. *)
        let v, venv =
          match ret with
            | None -> fresh_var ctx.ctx_venv typ loc
            | Some (v', _) -> v', ctx.ctx_venv in
        (* The call to execute the DFA closes the current block, and
           the success continuation begins in a new block (with the
           same rationale as for RE_non_term). *)
        let lsc = Label.fresh_label () in
        let nd = Node.N_exec_dfa (dfa, v, lsc, ctx.ctx_failcont) in
        let ctx = close_block {ctx with ctx_venv = venv} b nd in
        ctx, new_labeled_block lsc

    | RE_non_term (nt, None) ->
        (* The jump to the CFG for the non-term causes the current
           block to end and continue on success in a new block, with
           failure continuing in the current failcont.  This is
           simpler than making this a linear node, which would require
           continuing at the current offset in this block, i.e.
           require (re-)entry into a block at an offset.  It's much
           simpler instead to always enter a block at its beginning.
           However, this choice may be quite inefficient due to an
           overabundance of jumps, and may need revisiting once it
           works correctly.  *)
        (* create a new label and block for the success continuation *)
        let lsc = Label.fresh_label () in
        let nd =
          Node.N_call_nonterm (nt, [], ret, lsc, ctx.ctx_failcont) in
        let ctx = close_block ctx b nd in
        ctx, new_labeled_block lsc

    | RE_non_term (nt, Some args) ->
        let venv, args =
          List.fold_left (fun (venv, args) (i, a, e) ->
              (if a != Ast.A_eq
               then let err =
                      Unsupported_construct
                        (re.rule_elem_loc, "map-view assignment") in
                    raise (Error err));
              let ae, venv =
                Anf_exp.normalize_exp ctx.ctx_tenv venv e in
              (* allocate a variable to assign this to *)
              let v, venv = fresh_var venv e.expr_aux e.expr_loc in
              venv, (i, v, ae) :: args
            ) (ctx.ctx_venv, []) args in
        (* evaluation of inherited attributes is right-to-left *)
        let b, args =
          List.fold_left (fun (b, args) (i, v, ae) ->
              add_gnode b (N_assign (v, true, ae)) v.v_typ v.v_loc,
              (i, v) :: args
            ) (b, []) args in
        let lsc = Label.fresh_label () in
        let nd =
          Node.N_call_nonterm (nt, args, ret, lsc, ctx.ctx_failcont) in
        let ctx = close_block ctx b nd in
        {ctx with ctx_venv = venv}, new_labeled_block lsc

    (* binding for return values *)
    | RE_named (v, re') ->
        let v, venv = bind_var ctx.ctx_venv v typ in
        let ret' = Some (v, true) in
        let ctx, b =
          lower_rule_elem {ctx with ctx_venv = venv} b ret' re' in
        (* we might have our own return to bind *)
        let b = match ret with
            | None -> b
            | Some (v', fresh) ->
                let nd = N_assign (v', fresh, ae_of_av (av_of_var v)) in
                add_gnode b nd typ loc in
        ctx, b

    (* side-effects *)
    | RE_action {action_stmts = (stmts, retexp); _} ->
        let venv, astmts =
          List.fold_left (fun (venv, astmts) stmt ->
              let astmt, venv =
                Anf_exp.normalize_stmt ctx.ctx_tenv venv stmt in
              venv, (astmt :: astmts)
            ) (ctx.ctx_venv, []) stmts in
        let astmts = List.rev astmts in
        let b = add_gnode b (N_action astmts) typ loc in
        let b, venv =
          match retexp, ret with
            | None, None ->
                b, venv
            | None, Some (v, fresh) ->
                (* TODO: assert that typ is 'unit' *)
                let unit = ae_of_av (make_av (AV_lit PL_unit) typ loc) in
                let nd = N_assign (v, fresh, unit) in
                let b = add_gnode b nd typ loc in
                b, venv
            | Some _, None ->
                (* Consider it an error if the user is not binding the
                   return expression *)
                let err = Unbound_return_expr loc in
                raise (Error err)
            | Some e, Some (v, fresh) ->
                let ae, venv =
                  Anf_exp.normalize_exp ctx.ctx_tenv venv e in
                let nd = N_assign (v, fresh, ae) in
                let b = add_gnode b nd typ loc in
                b, venv in
        {ctx with ctx_venv = venv}, b

    (* control flow *)

    | RE_constraint c ->
        let cir, venv =
          Anf_exp.normalize_exp ctx.ctx_tenv ctx.ctx_venv c in
        (* if we don't have a return variable, generate one to hold
           the value of the constraint *)
        let cvar, venv, nd = match ret with
            | None ->
                let cvar, venv = fresh_var venv typ loc in
                let nd = N_assign (cvar, true, cir) in
                cvar, venv, nd
            | Some (v, fresh) ->
                let nd = N_assign (v, fresh, cir) in
                v, venv, nd in
        let b = add_gnode b nd typ loc in
        (* make a new block for the success continuation *)
        let lsc, bsc = new_block () in
        (* close the current block and update the ir *)
        let nd = Node.N_constraint (cvar, lsc, ctx.ctx_failcont) in
        let ctx = close_block ctx b nd in
        (* continue with the success continuation *)
        {ctx with ctx_venv = venv}, bsc

    (* since the case when there is no return value is especially
       simple, handle it separately *)
    | RE_seq res when ret = None ->
        List.fold_left (fun (ctx, b) re ->
            lower_rule_elem ctx b ret re
          ) (ctx, b) res

    (* with a return value, the outline is the same as above, but we
       have to ensure that the return variable is properly assigned *)
    | RE_seq res ->
        let ctx, b, vs =
          List.fold_left (fun (ctx, b, vs) (re: rule_elem) ->
              (* create variables for the elements of the sequence *)
              let v, venv =
                fresh_var ctx.ctx_venv re.rule_elem_aux re.rule_elem_loc in
              let ret = Some (v, true) in
              let ctx = {ctx with ctx_venv = venv} in
              let ctx, b = lower_rule_elem ctx b ret re in
              ctx, b, v :: vs
            ) (ctx, b, []) res in
        (* construct the list value holding the elements, starting
           with the base empty value *)
        let l = constr_av "[]" "[]" [] typ loc in
        (* since the vs are in reverse order, we can simply fold-left
           them into the list, getting them back into the original
           order *)
        let l = List.fold_left (fun l v ->
                    let av = av_of_var v in
                    constr_av "[]" "::" [av; l] l.av_typ l.av_loc
                  ) l vs in
        let l = ae_of_av l in
        let v, fresh = match ret with
            | None -> assert false (* handled above *)
            | Some (v, fresh) -> v, fresh in
        let b = add_gnode b (N_assign (v, fresh, l)) typ loc in
        ctx, b

    (* there is no special case for ret since it gets handled by
       whichever re succeeds *)
    | RE_choice res ->
        (* since any re could succeed, we need to create a common
           success continuation for all of them. *)
        let lsc = Label.fresh_label () in
        (* each re, except the last, needs to fail to the next one,
           and the last re should fail to the current failcont. *)
        let orig_failcont = ctx.ctx_failcont in
        assert (List.length res > 0);
        let fls = mk_choice_labels res orig_failcont in
        assert (List.length fls == List.length res);
        (* pair each re with its failcont *)
        let res = List.combine res fls in
        let ctx, _ = (* discard the last generated fail block *)
          List.fold_left (fun (ctx, b) (re, (fl, last)) ->
              let b = if not last
                      then add_node b (Node.N_push_failcont fl)
                      else b in
              let ctx = {ctx with ctx_failcont = fl} in
              let ctx, b = lower_rule_elem ctx b ret re in
              let b = if not last
                      then (* on success, pop the failcont *)
                        add_node b (Node.N_pop_failcont fl)
                      else b in
              (* jump to the success continuation *)
              let ctx = close_with_jump ctx b lsc in
              (* allocate the failure continuation of the current rule, into
                 which the next rule is lowered; if this is the last rule,
                 the new block is discarded *)
              ctx, new_labeled_block fl
            ) (ctx, b) res in
        (* continue with the success block and the original failcont.
           an invariant here is that any pushed failconts have been
           popped by the time this block is entered.  *)
        let b = new_labeled_block lsc in
        {ctx with ctx_failcont = orig_failcont}, b

    | RE_star (re', None) ->
        (* initialize the return value if any *)
        let vr, b = match ret with
            | None ->
                None, b
            | Some (vr, fresh) ->
                (* initialize vr to [] *)
                let null = constr_av "[]" "[]" [] typ loc in
                let nd = N_assign (vr, fresh, ae_of_av null) in
                let b = add_gnode b nd typ loc in
                Some vr, b in
        (* since (re')* can never fail, create a new label for the
           success cont (re')* which will be the failcont of re'.  the
           failcont needs to be pushed _after_ the assignment above,
           so that the assignment is remembered in case re' fails the
           first time.
         *)
        let lsc = Label.fresh_label () in
        let b = add_node b (Node.N_push_failcont lsc) in
        (* create a label for a new block for re' since it will be a
           jump target for the loop over re', and close the current
           block with a jump to the loop *)
        let lp = Label.fresh_label () in
        let ctx = close_with_jump ctx b lp in
        let b = new_labeled_block lp in
        (* lower re' into this block with the new failcont, adjusting
           for any return value *)
        let orig_failcont = ctx.ctx_failcont in
        let ctx = {ctx with ctx_failcont = lsc} in
        let ctx, b = match vr with
            | None ->
                lower_rule_elem ctx b None re'
            | Some vr ->
                (* create a variable for the matched value for re' *)
                let typ' = re'.rule_elem_aux in
                let loc' = re'.rule_elem_loc in
                let v, venv = fresh_var ctx.ctx_venv typ' loc' in
                (* Note: v' is fresh here, but inside a loop, which
                   means the freshness is only valid the first time
                   around.  This will be true in general, for
                   variables that are inside non-local loops. *)
                let ret' = Some (v, true) in
                let ctx = {ctx with ctx_venv = venv} in
                let ctx, b = lower_rule_elem ctx b ret' re' in
                (* update the return value:
                     vr := v :: vr , and reverse it when done *)
                let l =
                  constr_av "[]" "::" [av_of_var v;
                                       av_of_var vr] typ loc in
                let nd = N_assign (vr, false, ae_of_av l) in
                let b = add_gnode b nd typ loc in
                ctx, b in
        (* on success, this block loops back to lp *)
        let ctx = close_with_jump ctx b lp in
        (* continue with the success block, which will be entered only
           if re failed, i.e. via a popped failcont.  so there is no
           need to pop it here. *)
        let b = new_labeled_block lsc in
        (* continue with the original failcont *)
        let ctx = {ctx with ctx_failcont = orig_failcont} in
        (* adjust any return value *)
        let b = match vr with
            | None ->
                b
            | Some vr ->
                (* ensure the list is reversed:
                   vr := List.rev vr *)
                let ftyp = mk_func_type ctx typ typ in
                let f = mk_mod_member "List" "rev" ftyp loc in
                let l = make_ae (AE_apply (f, [av_of_var vr])) typ loc in
                add_gnode b (N_assign (vr, false, l)) typ loc in
        ctx, b

    | RE_star (re', Some e) ->
        (* The loop bound is tracked in a variable, and the return
           value is accumulated in a list that is reversed at the end.
           Note a big difference wrt RE_star (_, None): re* can never
           fail, but re^n can fail.
         *)
        let vr, b = match ret with
            | None ->
                None, b
            | Some (vr, fresh) ->
                (* initialize vr to [] *)
                let null = constr_av "[]" "[]" [] typ loc in
                let nd = N_assign (vr, fresh, ae_of_av null) in
                let b = add_gnode b nd typ loc in
                Some vr, b in
        (* Assign the bound to a variable bv, and then decrement this
           variable in a loop as re' is matched.  The loop terminates
           when the bv fails the constraint that it is positive. *)
        let bnd, venv =
          Anf_exp.normalize_exp ctx.ctx_tenv ctx.ctx_venv e in
        let bv, venv = fresh_var venv e.expr_aux e.expr_loc in
        let nd = N_assign (bv, true, bnd) in
        let b = add_gnode b nd e.expr_aux e.expr_loc in
        (* close the block with a jump to block containing the loop
           comparison *)
        let lc = Label.fresh_label () in
        let ctx = close_with_jump {ctx with ctx_venv = venv} b lc in
        (* the loop exit will be the success continuation *)
        let lx = Label.fresh_label () in
        (* the loop comparison block evaluates the bound constraint *)
        let b = new_labeled_block lc in
        (* build the boolean comparison variable: c := bv > 0 *)
        let bool = get_typ ctx "bool" in
        let z = av_of_int ctx 0 e.expr_loc in
        let ae = AE_binop (Ast.Gt, av_of_var bv, z) in
        let ae = make_ae ae bool e.expr_loc in
        let c, venv = fresh_var venv bool loc in
        let b = add_gnode b (N_assign (c, true, ae)) bool e.expr_loc in
        (* branch on c: true -> do re, false -> jump to exit *)
        let lre = Label.fresh_label () in
        let nd = Node.N_cond_branch (c, lre, lx) in
        let ctx = close_block {ctx with ctx_venv = venv} b nd in
        (* build the block for re', failing to the current failcont *)
        let b = new_labeled_block lre in
        (* lower re' into this block, adjusting for any return
           value *)
        let ctx, b = match vr with
            | None ->
                lower_rule_elem ctx b None re'
            | Some vr ->
                (* create a variable for the matched value for re' *)
                let typ' = re'.rule_elem_aux in
                let loc' = re'.rule_elem_loc in
                let v, venv = fresh_var ctx.ctx_venv typ' loc'  in
                (* Note: v' is fresh here, but inside a loop, which
                   means the freshness is only valid the first time
                   around.  This will be true in general, for
                   variables that are inside non-local loops. *)
                let ret' = Some (v, true) in
                let ctx = {ctx with ctx_venv = venv} in
                let ctx, b = lower_rule_elem ctx b ret' re' in
                (* update the return value:
                   vr := v :: vr , and reverse it when done *)
                let l =
                  constr_av "[]" "::" [av_of_var v;
                                       av_of_var vr] typ loc in
                let nd = N_assign (vr, false, ae_of_av l) in
                let b = add_gnode b nd typ loc in
                ctx, b in
        (* bv := bv - 1 *)
        let int = get_typ ctx "int" in
        let o = av_of_int ctx 1 e.expr_loc in
        let ae = AE_binop (Ast.Minus, av_of_var bv, o) in
        let ae = make_ae ae int e.expr_loc in
        let nd = N_assign (bv, true, ae) in
        let b = add_gnode b nd int e.expr_loc in
        (* close with a jump to the comparison *)
        let ctx = close_with_jump ctx b lc in
        (* continue with the exit block as success continuation *)
        let b = new_labeled_block lx in
        (* adjust any return value *)
        let b = match vr with
            | None ->
                b
            | Some vr ->
                (* ensure the list is reversed:
                   vr := List.rev vr *)
                let ftyp = mk_func_type ctx typ typ in
                let f = mk_mod_member "List" "rev" ftyp loc in
                let l = make_ae (AE_apply (f, [av_of_var vr])) typ loc in
                add_gnode b (N_assign (vr, false, l)) typ loc in
        ctx, b

    (* Since the RE_opt case differs a fair amount depending on
       whether there is a return variable to be bound, we keep the two
       cases separate. *)
    | RE_opt re' when ret == None ->
        (* re'? cannot fail, so create a new label that can be used
           for both the success and failure case, and save the
           original failure continuation. *)
        let lsc = Label.fresh_label () in
        let b = add_node b (Node.N_push_failcont lsc) in
        let orig_failcont = ctx.ctx_failcont in
        (* lower re' with the new failure continuation *)
        let ctx = {ctx with ctx_failcont = lsc} in
        let ctx, b = lower_rule_elem ctx b ret re' in
        (* on the success path, pop the failcont *)
        let b = add_node b (Node.N_pop_failcont lsc) in
        (* terminate the current block with a jump to the
           continuation block, since that is where the failure path
           will join us *)
        let ctx = close_with_jump ctx b lsc in
        let bsc = new_labeled_block lsc in
        (* continue with the original failure continuation *)
        {ctx with ctx_failcont = orig_failcont}, bsc

    (* with a return value, the outline is the same as above, but we
       have to ensure that the return variable is properly assigned in
       both the success as well as the failure case. *)
    | RE_opt re' ->
        (* create a new variable to contain the matched value, and new
           labels for the success and failure continuations. *)
        let lsc = Label.fresh_label () in
        let lfl = Label.fresh_label () in
        let vsc, venv =
          let typ' = re'.rule_elem_aux in
          let loc' = re'.rule_elem_loc in
          fresh_var ctx.ctx_venv typ' loc' in
        let ret' = Some (vsc, true) in
        (* save the original failure continuation, and prepare an
           updated context *)
        let orig_failcont = ctx.ctx_failcont in
        let ctx = {ctx with ctx_failcont = lfl; ctx_venv = venv} in
        (* push the failcont before lowering the re *)
        let b = add_node b (Node.N_push_failcont lfl) in
        let ctx, b = lower_rule_elem ctx b ret' re' in
        (* on the success path, pop the failcont first so that the
           assignment below holds *)
        let b = add_node b (Node.N_pop_failcont lfl) in
        (* extract the current return value *)
        let vr, fresh = match ret with
            | None -> assert false (* handled above *)
            | Some (vr, fresh) -> vr, fresh in
        (* use the return value from re' in vsc, construct
           'option::Some(vsc)' and bind it to vr *)
        let av = constr_av "option" "Some" [av_of_var vsc] typ loc in
        let nd = N_assign (vr, fresh, ae_of_av av) in
        let b = add_gnode b nd typ loc in
        (* close the current block by jumping to lsc *)
        let ctx = close_with_jump ctx b lsc in
        (* construct the failure block for lfl, in which vr gets
           assigned 'option::None' and then control jumps to lsc. *)
        let b = new_labeled_block lfl in
        let none = constr_av "option" "None" [] typ loc in
        let nd = N_assign (vr, fresh, ae_of_av none) in
        let b = add_gnode b nd typ loc in
        let ctx = close_with_jump ctx b lsc in
        (* construct the lsc continuation block, and continue with it
           as the current block, in a context where the original
           failure continuation is restored *)
        let b = new_labeled_block lsc in
        {ctx with ctx_failcont = orig_failcont}, b

    | RE_epsilon ->
        ctx, b

    (* view control *)

    | RE_set_view e ->
        let ae, venv =
          Anf_exp.normalize_exp ctx.ctx_tenv ctx.ctx_venv e in
        let v, venv = fresh_var venv e.expr_aux e.expr_loc in
        let nd = N_assign (v, true, ae) in
        let b = add_gnode b nd e.expr_aux loc in
        let unit = get_typ ctx "unit" in
        let b = add_gnode b (N_set_view v) unit loc in
        {ctx with ctx_venv = venv}, b

    (* Due to _set_view, variable state restoration after a
       failcont is decoupled from view restoration.  So views need to
       be restored explicitly after failures, unlike variable state. *)
    | RE_at_pos (e, re') ->
        let ae, venv =
          Anf_exp.normalize_exp ctx.ctx_tenv ctx.ctx_venv e in
        let v, venv = fresh_var venv e.expr_aux e.expr_loc in
        let nd = N_assign (v, true, ae) in
        let b = add_gnode b nd e.expr_aux e.expr_loc in
        (* Save the current view before the excursion *)
        let unit = get_typ ctx "unit" in
        let b = add_gnode b N_push_view unit loc in
        (* Update the view *)
        let b = add_gnode b (N_set_pos v) unit loc in
        (* The view needs to be restored on both the success and
           failure paths.  Create a new failcont which will first
           restore the view, and then return the original failcont. *)
        let lf = Label.fresh_label () in
        let orig_failcont = ctx.ctx_failcont in
        (* push the failcont *)
        let b = add_node b (Node.N_push_failcont lf) in
        (* lower the rule element with this failcont *)
        let ctx = {ctx with ctx_venv = venv; ctx_failcont = lf} in
        let ctx, b = lower_rule_elem ctx b ret re' in
        (* on the success path, restore the failcont and the view *)
        let b = add_node b (Node.N_pop_failcont lf) in
        let b = add_gnode b N_pop_view unit loc in
        let ctx = {ctx with ctx_failcont = orig_failcont} in
        (* create the trampoline failcont block that restores the view *)
        let tfb = new_labeled_block lf in
        let tfb = add_gnode tfb N_pop_view unit loc in
        let ctx = close_with_jump ctx tfb orig_failcont in
        (* proceed with the current block *)
        ctx, b

    | RE_at_view (e, re') ->
        (* essentially the same as above, but with the N_set_view primitive *)
        let ae, venv =
          Anf_exp.normalize_exp ctx.ctx_tenv ctx.ctx_venv e in
        let v, venv = fresh_var venv e.expr_aux e.expr_loc in
        let nd = N_assign (v, true, ae) in
        let b = add_gnode b nd e.expr_aux loc in
        (* Save the current view before the excursion *)
        let unit = get_typ ctx "unit" in
        let b = add_gnode b N_push_view unit loc in
        (* Update the view *)
        let b = add_gnode b (N_set_pos v) unit loc in
        (* The view needs to be restored on both the success and
           failure paths.  Create a new failcont which will first
           restore the view, and then return the original failcont. *)
        let lf = Label.fresh_label () in
        let orig_failcont = ctx.ctx_failcont in
        (* push the failcont *)
        let b = add_node b (Node.N_push_failcont lf) in
        (* lower the rule element with this failcont *)
        let ctx = {ctx with ctx_venv = venv; ctx_failcont = lf} in
        let ctx, b = lower_rule_elem ctx b ret re' in
        (* on the success path, restore the failcont and the view *)
        let b = add_node b (Node.N_pop_failcont lf) in
        let b = add_gnode b N_pop_view unit loc in
        let ctx = {ctx with ctx_failcont = orig_failcont} in
        (* create the trampoline failcont block that restores the view *)
        let tfb = new_labeled_block lf in
        let tfb = add_gnode tfb N_pop_view unit loc in
        let ctx = close_with_jump ctx tfb orig_failcont in
        (* proceed with the current block *)
        ctx, b

    (* handle the multi-assignment map-view case before the more
       general map-view case below *)
    | RE_map_views (e, ({rule_elem = RE_non_term (nt, Some args); _}
                        as re'))
         when List.exists (fun (_, a, _) -> a = Ast.A_in) args ->
        let ae, venv =
          Anf_exp.normalize_exp ctx.ctx_tenv ctx.ctx_venv e in
        let vl, venv = fresh_var venv e.expr_aux e.expr_loc in
        let nd = N_assign (vl, true, ae) in
        let b = add_gnode b nd e.expr_aux e.expr_loc in
        (* Split args into their types: iters are the variables
           holding the lists to be looped over (i.e. the condition
           variables), while consts are the variables holding values
           that don't change in the loop.  Note that `vl` holding the
           list of views is also a condition variable. *)
        let b, venv, iters, consts =
          List.fold_left (fun (b, venv, is, cs) (i, a, e) ->
              let ae, venv =
                Anf_exp.normalize_exp ctx.ctx_tenv venv e in
              (* allocate a variable for this value *)
              let v, venv = fresh_var venv e.expr_aux e.expr_loc in
              let nd = N_assign (v, true, ae) in
              let b = add_gnode b nd e.expr_aux e.expr_loc in
              let is, cs = match a with
                  | Ast.A_in -> (i, v) :: is, cs
                  | Ast.A_eq -> is, (i, v) :: cs in
              b, venv, is, cs
            ) (b, venv, [], []) args in
        (* initialize the return value if any *)
        let null = constr_av "[]" "[]" [] typ loc in
        let vr, b = match ret with
            | None ->
                None, b
            | Some (vr, fresh) ->
                let nd = N_assign (vr, fresh, ae_of_av null) in
                let b = add_gnode b nd typ loc in
                Some vr, b in
        (* save the current view: we will need to restore this in the
           success and failure paths. *)
        let unit = get_typ ctx "unit" in
        let b = add_gnode b N_push_view unit e.expr_loc in
        (* Create a sequence of condition blocks starting with `lc`
           that check if any of the looped-over lists are null.  If
           any is, go to the exit block `lx`, otherwise go to the next
           condition block.  The last condition block goes to the loop
           body block `lp`. *)
        let lc = Label.fresh_label () in
        let lx = Label.fresh_label () in
        (* jump to the starting condition block *)
        let ctx = close_with_jump {ctx with ctx_venv = venv} b lc in
        (* collect the list variables *)
        let vs = vl :: List.map snd iters in
        let ctx, lp =
          List.fold_left (fun (ctx, l) v ->
              (* create the condition block for `v` with label `l` *)
              let b = new_labeled_block l in
              let null = constr_av "[]" "[]" [] v.v_typ v.v_loc in
              let bool = get_typ ctx "bool" in
              let ae = AE_binop (Ast.Eq, (av_of_var v), null) in
              let ae = make_ae ae bool v.v_loc in
              let vc, venv = fresh_var ctx.ctx_venv bool v.v_loc in
              let nd = N_assign (vc, true, ae) in
              let b = add_gnode b nd bool v.v_loc in
              (* create a label for the next condition block *)
              let ln = Label.fresh_label () in
              let nd = Node.N_cond_branch (vc, lx, ln) in
              let ctx = close_block {ctx with ctx_venv = venv} b nd in
              ctx, ln
            ) (ctx, lc) vs in
        (* create the loop body block *)
        let b = new_labeled_block lp in
        (* Extract the heads of the various lists, and update the
           lists in the condition variables to their tails.  Collect
           the variables storing the heads in the same order as `vs`
           to make the call to the non-terminal *)
        let ctx, b, vvs =
          List.fold_left (fun (ctx, b, vvs) v ->
              (* get the head: vv = List.head(v) *)
              (* todo: use the _element type_ of the list type in
                 v.v_typ where appropriate below *)
              let ftyp = mk_func_type ctx v.v_typ v.v_typ in
              let f  = mk_mod_member "List" "head" ftyp v.v_loc in
              let hd =
                make_ae (AE_apply (f, [av_of_var v])) v.v_typ v.v_loc in
              let vv, venv = fresh_var ctx.ctx_venv v.v_typ v.v_loc in
              let nd = N_assign (vv, true, hd) in
              let b  = add_gnode b nd v.v_typ v.v_loc in
              (* update the list: v := List.tail(v) *)
              let f  = mk_mod_member "List" "tail" ftyp v.v_loc in
              let tl =
                make_ae (AE_apply (f, [av_of_var vl])) v.v_typ v.v_loc in
              let nd = N_assign (v, true, tl) in
              let b  = add_gnode b nd v.v_typ v.v_loc in
              {ctx with ctx_venv = venv}, b, vv :: vvs
            ) (ctx, b, []) vs in
        let vvs = List.rev vvs in (* the order should now match `vs` *)
        let vvl, vvis = List.hd vvs, List.tl vvs in
        (* `vvl` now holds the view to set, and `vvis` holds the
           view-specific values of the attributes in `iters` *)
        let viters = List.combine iters vvis in
        (* set the view: set_view(vvl) *)
        let nd = N_set_view vvl in
        let b  = add_gnode b nd unit vvl.v_loc in
        (* The view needs to be restored on both the success and
           failure paths.  Create a new failcont which will first
           restore the view, and then return the original failcont. *)
        let lf = Label.fresh_label () in
        (* push the failcont *)
        let b = add_node b (Node.N_push_failcont lf) in
        (* construct the inherited attr argument list for the call *)
        let iters' = List.map (fun ((i, _), vv) -> (i, vv)) viters in
        let args' = iters' @ consts in
        (* Construct a return value for non-terminal parse if needed,
           and the success continuation block for the call.
           Since the call terminates the current block, there needs to
           be an epilog block in the body to process any return
           value.  This epilog is not present if the return value is
           not needed.
         *)
        let ctx = match vr with
            | None ->
                (* there is no return value to process. after the
                   non-terminal call, the success continuation will be
                   the condition block, since all the condition
                   variables were updated at the beginning of this
                   body block. *)
                let nd = Node.N_call_nonterm (nt, args', None, lc, lf) in
                close_block ctx b nd
            | Some vr ->
                (* construct the variable to hold the return value *)
                let typ' = re'.rule_elem_aux in
                let loc' = re'.rule_elem_loc in
                let v, venv = fresh_var ctx.ctx_venv typ' loc' in
                let ret' = Some (v, true) in
                (* create a label for the epilog block in which to
                   accumulate the return value; this epilog will form
                   the success continuation for the call *)
                let le = Label.fresh_label () in
                let nd = Node.N_call_nonterm (nt, args', ret', le, lf) in
                let ctx = close_block {ctx with ctx_venv = venv} b nd in
                (* now accumulate the return value *)
                let b = new_labeled_block le in
                (* update the return value:
                   vr := v :: vr , and reverse it when done *)
                let l =
                  constr_av "[]" "::" [av_of_var v;
                                       av_of_var vr] typ loc in
                let nd = N_assign (vr, false, ae_of_av l) in
                let b = add_gnode b nd typ loc in
                (* continue to the condition block for the loop *)
                close_with_jump ctx b lc in
        (* create the trampoline failcont block that restores the view *)
        let tfb = new_labeled_block lf in
        let tfb = add_gnode tfb N_pop_view unit loc in
        let ctx = close_with_jump ctx tfb ctx.ctx_failcont in
        (* restore the view in the exit block *)
        let b = new_labeled_block lx in
        let b = add_gnode b N_pop_view unit e.expr_loc in
        (* reverse the return value since we're done *)
        let b = match vr with
            | None ->
                b
            | Some vr ->
                (* vr := List.rev vr *)
                let ftyp = mk_func_type ctx typ typ in
                let f = mk_mod_member "List" "rev" ftyp loc in
                let l = make_ae (AE_apply (f, [av_of_var vr])) typ loc in
                add_gnode b (N_assign (vr, false, l)) typ loc in
        ctx, b

    | RE_map_views (e, re') ->
        let ae, venv =
          Anf_exp.normalize_exp ctx.ctx_tenv ctx.ctx_venv e in
        let vl, venv = fresh_var venv e.expr_aux e.expr_loc in
        let nd = N_assign (vl, true, ae) in
        let b = add_gnode b nd e.expr_aux e.expr_loc in
        (* initialize the return value if any *)
        let null = constr_av "[]" "[]" [] typ loc in
        let vr, b = match ret with
            | None ->
                None, b
            | Some (vr, fresh) ->
                let nd = N_assign (vr, fresh, ae_of_av null) in
                let b = add_gnode b nd typ loc in
                Some vr, b in
        (* save the current view: we will need to restore this in the
           success and failure paths *)
        let unit = get_typ ctx "unit" in
        let b = add_gnode b N_push_view unit e.expr_loc in
        (* create a block for the loop condition and jump to it *)
        let lc = Label.fresh_label () in
        let ctx =
          close_with_jump {ctx with ctx_venv = venv} b lc in
        let b = new_labeled_block lc in
        (* vc := v == [] *)
        let bool = get_typ ctx "bool" in
        let ae = AE_binop (Ast.Eq, (av_of_var vl), null) in
        let ae = make_ae ae bool e.expr_loc in
        let vc, venv = fresh_var ctx.ctx_venv bool e.expr_loc in
        let nd = N_assign (vc, true, ae) in
        let b = add_gnode b nd bool e.expr_loc in
        (* create a label for the loop body block and its exit block *)
        let lp = Label.fresh_label () in
        let lx = Label.fresh_label () in
        (* if vc, we exit the loop, else we enter it *)
        let nd = Node.N_cond_branch (vc, lx, lp) in
        let ctx = close_block {ctx with ctx_venv = venv} b nd in
        (* create the loop body block *)
        let b = new_labeled_block lp in
        (* get the view to set: vv = List.head(vl) *)
        (* todo: use the _element type_ of the list type in e.expr_aux
           where appropriate below *)
        let ftyp = mk_func_type ctx e.expr_aux e.expr_aux in
        let f = mk_mod_member "List" "head" ftyp e.expr_loc in
        let hd =
          make_ae (AE_apply (f, [av_of_var vl])) e.expr_aux e.expr_loc in
        let vv, venv = fresh_var venv e.expr_aux e.expr_loc in
        let nd = N_assign (vv, true, hd) in
        let b  = add_gnode b nd e.expr_aux e.expr_loc in
        (* update the remaining views: vl = List.tail(vl) *)
        let f = mk_mod_member "List" "tail" ftyp e.expr_loc in
        let tl =
          make_ae (AE_apply (f, [av_of_var vl])) e.expr_aux e.expr_loc in
        let nd = N_assign (vl, true, tl) in
        let b  = add_gnode b nd e.expr_aux e.expr_loc in
        (* set the view: set_view(vv) *)
        let nd = N_set_view vv in
        let b  = add_gnode b nd unit e.expr_loc in
        (* The view needs to be restored on both the success and
           failure paths.  Create a new failcont which will first
           restore the view, and then return the original failcont. *)
        let lf = Label.fresh_label () in
        let orig_failcont = ctx.ctx_failcont in
        (* push the failcont *)
        let b = add_node b (Node.N_push_failcont lf) in
        (* lower the rule element with this failcont, adjusting for
           any return value *)
        let ctx, b = match vr with
            | None ->
                lower_rule_elem {ctx with ctx_venv = venv;
                                          ctx_failcont = lf} b None re'
            | Some vr ->
                (* create a new variable to hold a matched value for re' *)
                let typ' = re'.rule_elem_aux in
                let loc' = re'.rule_elem_loc in
                let v, venv = fresh_var venv typ' loc' in
                let ret' = Some (v, true) in
                let ctx =
                  {ctx with ctx_venv = venv; ctx_failcont = lf} in
                let ctx, b = lower_rule_elem ctx b ret' re' in
                (* update the return value:
                   vr := v :: vr , and reverse it when done *)
                let l =
                  constr_av "[]" "::" [av_of_var v;
                                       av_of_var vr] typ loc in
                let nd = N_assign (vr, false, ae_of_av l) in
                let b = add_gnode b nd typ loc in
                ctx, b in
        (* on the success path, restore the failcont *)
        let b = add_node b (Node.N_pop_failcont lf) in
        let ctx = {ctx with ctx_failcont = orig_failcont} in
        (* loop back to the condition *)
        let ctx = close_with_jump ctx b lc in
        (* create the trampoline failcont block that restores the view *)
        let tfb = new_labeled_block lf in
        let tfb = add_gnode tfb N_pop_view unit e.expr_loc in
        let ctx = close_with_jump ctx tfb orig_failcont in
        (* restore the view in the exit block *)
        let b = new_labeled_block lx in
        let b = add_gnode b N_pop_view unit e.expr_loc in
        (* reverse the return value since we're done *)
        let b = match vr with
            | None ->
                b
            | Some vr ->
                (* vr := List.rev vr *)
                let ftyp = mk_func_type ctx typ typ in
                let f = mk_mod_member "List" "rev" ftyp loc in
                let l = make_ae (AE_apply (f, [av_of_var vr])) typ loc in
                add_gnode b (N_assign (vr, false, l)) typ loc in
        ctx, b

(* unlike a rule element, a rule has no explicit return value, since
   the 'return values' of a rule are assigned by the actions within a
   well-typed rule *)
let lower_rule (ctx: context) (b: opened) (r: rule)
    : (context * opened) =
  (* set a failcont to collect the temporaries *)
  let fl = Label.fresh_label () in
  let orig_failcont = ctx.ctx_failcont in
  let b = add_node b (Node.N_push_failcont fl) in
  (* initialize the rule temporaries *)
  let b, venv =
    List.fold_left (fun (b, venv) (v, _, (e: exp)) ->
        let v, venv = bind_var venv v e.expr_aux in
        let ae, venv =
          Anf_exp.normalize_exp ctx.ctx_tenv venv e in
        let nd = N_assign (v, true, ae) in
        let b = add_gnode b nd e.expr_aux e.expr_loc in
        b, venv
      ) (b, ctx.ctx_venv) r.rule_temps in
  (* now lower the rule elements *)
  let ctx, b =
    List.fold_left (fun (ctx, b) re ->
        lower_rule_elem ctx b None re
      ) ({ctx with ctx_venv = venv}, b) r.rule_rhs in
  (* pop the failcont *)
  let b = add_node b (Node.N_pop_failcont fl) in
  (* in the failcont, jump to the original one *)
  let fb = new_labeled_block fl in
  let ctx = close_with_jump {ctx with ctx_failcont = orig_failcont}
              fb orig_failcont in
  ctx, b

(* a non-terminal requires the set up of its attributes and lowering
   of the ordered choice of its rules; in addition, it needs an
   nt_entry so that it can be called from other rules. *)
let lower_general_ntd (ctx: context) (ntd: non_term_defn) : context =
  let nt_name = Location.value ntd.non_term_name in
  let typ = get_nt_typ ctx nt_name in
  (* ensure the NT var is bound in the rules *)
  let venv = match ntd.non_term_varname with
      | None ->
          ctx.ctx_venv
      | Some v ->
          let _, venv = bind_var ctx.ctx_venv v typ in
          venv in
  (* and similarly for the inherited attributes *)
  let tenv = ctx.ctx_tenv in
  let nt_inh_attrs, venv =
    List.fold_left (fun (attrs, venv) (v, te) ->
        let ia = Ast.var_name v in
        (* todo: move this into a convenient util *)
        let te = TypedAstUtils.expand_type_abbrevs tenv te in
        let typ = TypeConv.intern tenv te in
        let v, venv = bind_var venv v typ in
        (Misc.StringMap.add ia (v, typ) attrs), venv
      ) (Misc.StringMap.empty, venv) ntd.non_term_inh_attrs in
  (* create the success and failure conts *)
  let lsucc = Label.fresh_label () in
  let lfail = Label.fresh_label () in
  (* create the entry block *)
  let lent, b = new_block () in
  (* create the intermediate failure conts needed to fail one rule to
     the next, with the final rule failing to lfail *)
  let fls = mk_choice_labels ntd.non_term_rules lfail in
  assert (List.length fls == List.length ntd.non_term_rules);
  (* pair each rule with its failcont *)
  let rls = List.combine ntd.non_term_rules fls in
  let ctx, _ = (* discard the last generated block *)
    List.fold_left (fun (ctx, b) (r, (fl, last)) ->
        let b = if not last
                then add_node b (Node.N_push_failcont fl)
                else b in
        let ctx = {ctx with ctx_failcont = fl} in
        let ctx, b = lower_rule ctx b r in
        let b = if not last
                then (* on success, pop the failcont *)
                  add_node b (Node.N_pop_failcont fl)
                else b in
        (* jump to the success continuation *)
        let ctx = close_with_jump ctx b lsucc in
        (* allocate the failure continuation of the current rule, into
           which the next rule is lowered; if this is the last rule,
           the new block is discarded *)
        ctx, new_labeled_block fl
      ) ({ctx with ctx_venv = venv}, b) rls in

  (* construct the nt_entry *)
  let nte =
    {nt_name = ntd.non_term_name;
     nt_inh_attrs;
     nt_typ = typ;
     nt_entry = lent;
     nt_succcont = lsucc;
     nt_failcont = lfail;
     nt_loc = ntd.non_term_loc} in
  (* add it to the ToC *)
  let toc = FormatToC.add nt_name nte ctx.ctx_toc in
  {ctx with ctx_toc = toc}

(* a wrapper to intercept the special case of a non-terminal without
   attributes and a single regexp-convertible rule with no
   temporaries *)
let lower_ntd (ctx: context) (ntd: non_term_defn) : context =
  (* detect special case *)
  let no_synth_attrs =
    match ntd.non_term_syn_attrs with
      | ALT_decls [] -> true
      | _                -> false in
  let no_inh_attrs = List.length ntd.non_term_inh_attrs = 0 in
  let is_regexp_rule, rl =
    match ntd.non_term_rules with
      | [] ->
          (* should have had a parse error *)
          assert false
      | [r] ->
          List.length r.rule_temps = 0
          && List.for_all
               (TypedAstUtils.is_regexp_elem ctx.ctx_tenv)
               r.rule_rhs,
          r
      | r :: _ ->
          false, r in
  (* update re context if needed *)
  let ctx =
    if no_synth_attrs && no_inh_attrs && is_regexp_rule
    then
      (* construct a regexp from the rule element sequence *)
      let re = match rl.rule_rhs with
          | [] -> assert false
          | h :: _ -> (* copy aux info *)
              Ast.({rule_elem = RE_seq_flat rl.rule_rhs;
                    rule_elem_loc = rl.rule_loc;
                    rule_elem_aux = h.rule_elem_aux}) in
      let rx = TypedAstUtils.to_regexp re in
      let rx = Cfg_regexp.build_re ctx.ctx_re_env rx in
      (* add this to the re environment *)
      let renv = Dfa.StringMap.add
                   (Location.value ntd.non_term_name)
                   (rl.rule_loc, rx)
                   ctx.ctx_re_env in
      {ctx with ctx_re_env = renv}
    else ctx in
  (* now dispatch to general case *)
  lower_general_ntd ctx ntd
