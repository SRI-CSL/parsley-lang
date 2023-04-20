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
open Site
open Anf
open Scf

(* An optional variable to which the matched return value needs to be
   bound. *)
type return = var option

(* type utilities *)

(* Extract out the element type of a list type.  This should only be
   called for ground list types. *)
let list_elem (t: TypedAst.typ) : TypedAst.typ =
  let qs, (_, lt, ts, _, _, _) =
    TypeEnvPrinter.term_type_info false t in
  assert (List.length qs = 0);
  assert (List.length ts = 1);
  assert (lt = (Ast.(Modul Mod_stdlib), Ast.TName "[]"));
  let TypeEnvPrinter.(Arg le) = List.hd ts in
  let tv, _, ts, _, _, _ = le in
  assert (List.length ts = 0);
  CoreAlgebra.TVariable tv

let is_unit (t: TypedAst.typ) : bool =
  let qs, (_, t, ts, _, _, _) =
    TypeEnvPrinter.term_type_info false t in
  (List.length qs = 0) && (List.length ts = 0)
  && t = (Ast.(Modul Mod_stdlib), Ast.TName "unit")

(* type and expression utilities *)

let mk_ident (n: string) l =
  Location.mk_loc_val n l

let mk_mod_member (m: string) (v: string) t l =
  let m = Location.mk_loc_val m l in
  let v = Location.mk_loc_val v l in
  make_av (AV_mod_member (m, v)) t l

let mk_mod_func (m: string) (v: string) t l =
  let m = Location.mk_loc_val m l in
  let v = Location.mk_loc_val v l in
  make_fv (FV_mod_member (m, v)) t l

let mk_func_type ctx arg res =
  TypeAlgebra.arrow (TypingEnvironment.as_fun ctx.ctx_tenv)
    arg res

let get_std_typ ctx name =
  let typ = Ast.TName name in
  let m   = AstUtils.stdlib in
  TypingEnvironment.typcon_variable ctx.ctx_tenv (m, typ)

let get_nt_typ ctx m name =
  let nt = Ast.NName name in
  match TypingEnvironment.lookup_non_term_type
          ctx.ctx_tenv (m, nt) with
    | Some t -> t
    | None -> assert false

(* ANF variable utilities *)

let fresh_var ctx typ loc =
  let vid, venv = VEnv.gen ctx.ctx_venv in
  make_var vid ctx.ctx_frame typ loc,
  {ctx with ctx_venv = venv}

let bind_var ctx v t =
  let v', venv = VEnv.bind ctx.ctx_venv v in
  let var = make_var v' ctx.ctx_frame t (Location.loc v) in
  let sv = mk_site_var v SV_val var in
  let fvs = StringMap.add (Ast.var_name v) sv ctx.ctx_free_vars in
  var, {ctx with ctx_venv      = venv;
                 ctx_free_vars = fvs}

(* ANF value utilities *)

let av_of_int ctx i num_t loc =
  let n = Ast.str_of_num_t num_t in
  let t = get_std_typ ctx n in
  make_av (AV_lit (PL_int (i, num_t))) t loc

let constr_av t c args typ loc =
  (* This module only constructs values in the stdlib. *)
  let m = Anf_common.M_stdlib in
  make_av (AV_constr ((m, t, c), args)) typ loc

(* enter and exit bitmode *)

let enter_bitmode (ctx: context) (b: block) (loc: Location.t)
    : context * block =
  if   ctx.ctx_bitmode
  then ctx, b
  else let typ = get_std_typ ctx "unit" in
       let id  = ctx.ctx_id_gen () in
       let s, ctx = mk_site ctx SS_bitmode loc in
       {ctx with ctx_bitmode = true},
       add_instr (mk_l2b L_enter_bitmode typ loc id (Some s)) b

let exit_bitmode (ctx: context) (b: block) (loc: Location.t)
    : context * block =
  if   not ctx.ctx_bitmode
  then ctx, b
  else let typ = get_std_typ ctx "unit" in
       let id  = ctx.ctx_id_gen () in
       let s, ctx = mk_site ctx SS_bitmode loc in
       {ctx with ctx_bitmode = false},
       add_instr (mk_l2b L_exit_bitmode typ loc id (Some s)) b

(* handle inserting a mark_bit_cursor if needed for a return value *)
let prepare_cursor
      (ctx: context) (b: block) (ret: return) (loc: Location.t)
    : block =
  match ret with
    | Some _ ->
        (* no other sensible type for mark_bit_cursor *)
        let typ = get_std_typ ctx "unit" in
        let id  = ctx.ctx_id_gen () in
        add_instr (mk_l2b L_mark_bit_cursor typ loc id None) b
    | None ->
        b

(* collect matched bits into a variable if needed *)
let collect_cursor
      (b: block) (pred: matched_bits_bound) (ret: return) (typ: TypedAst.typ)
      (obf: TypingEnvironment.bitfield_info option) (loc: Location.t)
      (id: instr_id)
    : block =
  match ret with
    | Some v ->
        let li = L_collect_bits (v, pred, obf) in
        add_instr (mk_l2b li typ loc id None) b
    | None ->
        b

(* wrappers for context munging *)

let norm_exp ctx e =
  let ae, ec' = Anf_gen.normalize_exp (to_exp_ctx ctx) e in
  ae, of_exp_ctx ctx ec'

let norm_const ctx c =
  let ac, ec' = Anf_gen.normalize_const (to_exp_ctx ctx) c in
  ac, of_exp_ctx ctx ec'

let norm_fun ctx f =
  let af, ec' = Anf_gen.normalize_fun (to_exp_ctx ctx) f in
  af, of_exp_ctx ctx ec'

let norm_recfuns ctx fs =
  let afs, ec' = Anf_gen.normalize_recfuns (to_exp_ctx ctx) fs in
  afs, of_exp_ctx ctx ec'

let norm_stms ctx stms =
  let sc, astms, span =
    List.fold_left (fun (sc, astms, span) stm ->
        let astm, sc = Anf_gen.normalize_stmt sc stm in
        let span = Location.extent span stm.stmt_loc in
        sc, astm :: astms, span
      ) (to_stm_ctx ctx, [], Location.ghost_loc) stms in
  let astm = match astms with
      | [s] -> s
      | _   -> {astmt      = AS_block (List.rev astms);
                astmt_loc  = span;
                astmt_site = None} in
  astm, of_stm_ctx ctx sc

(* From a control-flow viewpoint, the choice combinator within a rule
   functions similarly to the rules for a non-terminal: the rules form
   an ordered choice of productions for the non-terminal.  The CFG
   construction hence is similar, and could be unified into a single
   function.  However, the APIs of the lowering functions,
   `lower_rule_elem` and `lower_rule` are different, due to the
   difference between the two types of ordered-choice: the match of
   choice combinator can be bound to a variable, while the match of a
   rule cannot be so bound.

   The API to the function is:
   . the `b` argument is the block in which the lowering function
     `lower_fn` should start lowering the choices.

   . the return values are: the updated context, and the updated block
     containing the instructions for the choices.
 *)
let lower_choices loc (ctx: context) (b: block)
      choices choice_loc_fn lower_fn : context * block =
  (* [[v=(RE_choice res)]] =
          [ start_choice(V) [ (* saves vars in V and the current view *)
              { do [ [[v=(re_i)]]
                     finish_choice ]
                handle Succ [ continue_choice ]
              } (* i = 0 ... N-2,
                   where N is the number of choices. *)
              do [ [[re_{N-1}]]
                   finish_choice ]
              handle Fail [ fail_choice ] (* No need to save view *)
          ]

          (* We get here when the first choice succeeds
             (i.e. when the first `finish_choice` executes).  We
             don't get here if all choices fail. *)
   *)
  let unit  = get_std_typ ctx "unit" in
  let mk_do (b: block) (is_last: bool) loc : bivalent_instr =
    let b, ctx =
      let id = ctx.ctx_id_gen () in
      let s, ctx  = mk_site ctx SS_choice loc in
      let li = L_finish_choice in
      add_instr (mk_l2b li unit loc id (Some s)) b,
      ctx in
    let b = seal_block b in
    (* The last handler fails the choice. *)
    let hf, li = (if   is_last
                  then H_failure, L_fail_choice
                  else H_success, L_continue_choice) in
    let h, ctx =
      let id = ctx.ctx_id_gen () in
      let s, ctx = mk_site ctx SS_choice loc in
      add_instr (mk_linst li unit loc id (Some s)) init_block,
      ctx in
    let di = C_do (b, (hf, seal_handler h)) in
    let id = ctx.ctx_id_gen () in
    mk_c2b di loc id None in
  let input_ctx = ctx in
  (* Allocate a choice frame, update the context. *)
  let cfrm = ctx.ctx_frame_gen () in
  let ctx = add_frame ctx cfrm in
  (* Lower each choice into its own do block. *)
  let ctx, dis, _ =
    List.fold_left (fun (ctx, dis, is_last) c ->
        (* Save and restore free vars across combinator. *)
        let fvs = ctx.ctx_free_vars in
        let ctx, b = lower_fn ctx init_block c in
        let ctx = {ctx with ctx_free_vars = fvs} in
        let di = mk_do b is_last (choice_loc_fn c) in
        ctx, di :: dis, false)
      (* Process `choices` in reverse order so that the last one is
         first, since it needs special handling. *)
      ({ctx with ctx_mutations = FrameMap.empty}, [], true)
      (List.rev choices) in
  (* Sequence the dos ... *)
  let cb = List.fold_left (fun b i -> add_instr i b)
             init_block dis in
  (* ... along with their mutations ... *)
  let cmuts = ctx.ctx_mutations in
  (* ... into a choice control block ... *)
  let ci = C_start_choices (cfrm, cmuts, seal_block cb) in
  let b, ctx =
    let id = ctx.ctx_id_gen () in
    let s, ctx  = mk_site ctx SS_choice loc in
    add_instr (mk_c2b ci loc id (Some s)) b,
    ctx in
  (* Pop the choice frame from the context. *)
  let ctx = pop_frame ctx in
  (* Fold the mutations into input mutations. *)
  let muts = FrameMap.union (fun _ ma mb ->
                 Some (union_mutations ma mb)
               ) input_ctx.ctx_mutations cmuts in
  (* Update the context with the merged mutations. *)
  {ctx with ctx_mutations = muts}, b

(* Note: The code generation often involves glue code in ANF. Ideally,
   this glue code would be constructed in the AST form, then run
   through the type-checker, then normalized via `Anf_gen`; this would
   ensure type-correctness.

   However, the below implemention loses the link between the ANF vars
   in the generated instructions and the constructed ANF, since fresh
   and unrelated ANF vars are created during `Anf_gen` normalization.
   It appears that modifying `Anf_gen` to handle both cases
   (i.e. source AST -> ANF as well as constructed AST -> ANF) would
   make the current `Anf_gen` overly complicated.  It would be good to
   fix this via some restructuring. *)

let rec lower_rule_elem (trace: bool) (ctx: context) (m: Ast.mname)
          (b: block) (ret: return) (re: TypedAst.rule_elem)
        : (context * block) =
  let typ = re.rule_elem_aux in
  let loc = re.rule_elem_loc in

  (* useful types *)
  let unit  = get_std_typ ctx "unit" in
  let bool  = get_std_typ ctx "bool" in
  let usize = get_std_typ ctx "usize" in

  (* wrapper for return variable *)
  let get_ret_var ctx ret =
    (* Bind a new var for the matched value if we don't have a
       return binding. *)
    match ret with
      | None    -> fresh_var ctx typ loc
      | Some v' -> v', ctx in

  match re.rule_elem with
    (* bit-level support *)

    | RE_bitvector bits ->
        (* main block *)
        let b' = init_block in
        let ctx, b' = enter_bitmode ctx b' loc in
        let b' = prepare_cursor ctx b' ret loc in
        let bits = Location.value bits in
        let b' =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_binst (B_bits bits) loc id None) b' in
        let pred = MB_exact bits in
        let b' =
          let id = ctx.ctx_id_gen () in
          collect_cursor b' pred ret typ None loc id in
        let b' = seal_block b' in
        (* failure handler *)
        let fail = init_block in
        let fail, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_fail_bitmode in
          let s, ctx  = mk_site ctx SS_bitmode loc in
          add_instr (mk_linst li unit loc id (Some s)) fail,
          ctx in
        let fail = seal_handler fail in
        (* control block *)
        let cblock =
          let id = ctx.ctx_id_gen () in
          mk_c2b (C_do (b', (H_failure, fail))) loc id None in
        (* add control block to the input block *)
        ctx, add_instr cblock b

    | RE_align bits ->
        (* main block *)
        let b' = init_block in
        let ctx, b' = enter_bitmode ctx b' loc in
        let b' = prepare_cursor ctx b' ret loc in
        let bits = Location.value bits in
        let b' =
          let id = ctx.ctx_id_gen () in
          let bi = B_align bits in
          add_instr (mk_binst bi loc id None) b' in
        let pred = MB_below bits in
        let b' =
          let id = ctx.ctx_id_gen () in
          collect_cursor b' pred ret typ None loc id in
        let b' = seal_block b' in
        (* failure handler *)
        let fail = init_block in
        let fail, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_fail_bitmode in
          let s, ctx  = mk_site ctx SS_bitmode loc in
          add_instr (mk_linst li unit loc id (Some s)) fail,
          ctx in
        let fail = seal_handler fail in
        (* control block *)
        let cblock =
          let id = ctx.ctx_id_gen () in
          mk_c2b (C_do (b', (H_failure, fail))) loc id None in
        (* add control block to the input block *)
        ctx,  add_instr cblock b

    | RE_bitfield bf ->
        (* This is equivalent to RE_bitvector for the underlying
           number of bits.  The interpretation of the matched value as
           a bitfield record is done by the record accessors. *)
        let bfi =
          TypedAstUtils.lookup_bitfield_info ctx.ctx_tenv m bf in
        let bits = bfi.bf_length in
        (* main block *)
        let b' = init_block in
        let ctx, b' = enter_bitmode ctx b' loc in
        let b' = prepare_cursor ctx b' ret loc in
        let b' =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_binst (B_bits bits) loc id None) b' in
        let pred = MB_exact bits in
        let b' =
          let id = ctx.ctx_id_gen () in
          collect_cursor b' pred ret typ None loc id in
        let b' = seal_block b' in
        (* failure handler *)
        let fail = init_block in
        let fail, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_fail_bitmode in
          let s, ctx  = mk_site ctx SS_bitmode loc in
          add_instr (mk_linst li unit loc id (Some s)) fail,
          ctx in
        let fail = seal_handler fail in
        (* control block *)
        let id = ctx.ctx_id_gen () in
        let cb = mk_c2b (C_do (b', (H_failure, fail))) loc id None in
        (* add control block to the input block *)
        ctx, add_instr cb b

    | RE_pad (bits, pat) ->
        (* Padding is like a bit-level constraint node in terms of
           its control flow. *)
        let bits = Location.value bits in
        (* main block *)
        let b' = init_block in
        let ctx, b' = enter_bitmode ctx b' loc in
        let b' = prepare_cursor ctx b' ret loc in
        let b' =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_binst (B_pad bits) loc id None) b' in
        let pred = MB_below bits, pat in
        let id = ctx.ctx_id_gen () in
        let chk = mk_binst (match ret with
                              | Some v -> B_collect_checked_bits (v, pred)
                              | None   -> B_check_bits pred)
                    loc id None in
        let b' = add_instr chk b' in
        let b' = seal_block b' in
        (* failure handler *)
        let fail = init_block in
        let fail, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_fail_bitmode in
          let s, ctx  = mk_site ctx SS_bitmode loc in
          add_instr (mk_linst li unit loc id (Some s)) fail,
          ctx in
        let fail = seal_handler fail in
        (* control block *)
        let id = ctx.ctx_id_gen () in
        let cb = mk_c2b (C_do (b', (H_failure, fail))) loc id None in
        (* add control block to the input block *)
        ctx, add_instr cb b

    (* other basic primitives *)

    | RE_regexp r ->
        let ctx, b = exit_bitmode ctx b loc in
        (* Compile the regexp into a DFA. *)
        let dfa = Dfa.Dfa_of_regexp.build_dfa trace ctx.ctx_re_env r in
        (* Bind a new var for the matched value if we don't have a
           return binding. *)
        let v, ctx = get_ret_var ctx ret in
        (* Add the DFA matcher instruction. *)
        let b, ctx =
          let id = ctx.ctx_id_gen () in
          let bi = B_exec_dfa (dfa, v) in
          let s, ctx  = mk_site ctx SS_regex loc in
          add_instr (mk_binst bi loc id (Some s)) b,
          ctx in
        ctx, b

    | RE_seq_flat _ ->
        let ctx, b = exit_bitmode ctx b loc in
        assert (TypedAstUtils.is_regexp_elem ctx.ctx_tenv m re);
        let rx = TypedAstUtils.rule_elem_to_regexp re in
        (* Now do as above *)
        (* Compile the regexp into a DFA. *)
        let dfa = Dfa.Dfa_of_regexp.build_dfa trace ctx.ctx_re_env rx in
        (* Bind a new var for the matched value if we don't have a
           return binding. *)
        let v, ctx = get_ret_var ctx ret in
        (* Add the DFA matcher instruction. *)
        let id = ctx.ctx_id_gen () in
        let bi = B_exec_dfa (dfa, v) in
        let s, ctx  = mk_site ctx SS_regex loc in
        ctx, add_instr (mk_binst bi loc id (Some s)) b

    | RE_scan scan ->
        let ctx, b = exit_bitmode ctx b loc in
        let v, ctx = get_ret_var ctx ret in
        let b =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_binst (B_scan (scan, v)) loc id None) b in
        ctx, b

    | RE_non_term (m, nt, None) ->
        let ctx, b = exit_bitmode ctx b loc in
        let v, ctx = get_ret_var ctx ret in
        let m  = Anf_common.modul_of_mname m in
        let id = ctx.ctx_id_gen () in
        let bi = B_call_nonterm (m, nt, [], v) in
        let s, ctx  = mk_site ctx SS_call loc in
        let call = mk_binst bi loc id (Some s) in
        ctx, add_instr call b

    | RE_non_term (m, nt, Some args) ->
        let ctx, b = exit_bitmode ctx b loc in
        let ctx, args =
          List.fold_left (fun (ctx, args) (i, a, e) ->
              (if   a != Ast.A_eq
               then let err = Unsupported_construct "map-view assignment" in
                    raise (Error (re.rule_elem_loc, err)));
              let ae, ctx = norm_exp ctx e in
              (* allocate a variable to assign this to *)
              let v, ctx = fresh_var ctx e.expr_aux e.expr_loc in
              ctx, (i, v, ae) :: args
            ) (ctx, []) args in
        (* evaluation of inherited attributes is right-to-left *)
        let b, args =
          List.fold_left (fun (b, args) (i, v, ae) ->
              let id = ctx.ctx_id_gen () in
              let li = L_assign (v, ae) in
              add_instr (mk_l2b li v.v_typ v.v_loc id None) b,
              (i, v) :: args
            ) (b, []) args in
        let v, ctx = get_ret_var ctx ret in
        let m = Anf_common.modul_of_mname m in
        let id = ctx.ctx_id_gen () in
        let bi = B_call_nonterm (m, nt, args, v) in
        let s, ctx  = mk_site ctx SS_call loc in
        let call = mk_binst bi loc id (Some s) in
        ctx, add_instr call b

    (* binding for return values *)
    | RE_named (v, re') ->
        (* Allow naming regardless of the current bit-mode.  This
           enables naming of bitwise matches. *)
        let v, ctx = bind_var ctx v typ in
        let ret' = Some v in
        let ctx, b =
          lower_rule_elem trace ctx m b ret' re' in
        (* we might have our own return to bind *)
        let b = match ret with
            | None ->
                b
            | Some v' ->
                let assign = L_assign (v', ae_of_av (av_of_var v)) in
                let id = ctx.ctx_id_gen () in
                add_instr (mk_l2b assign v.v_typ v.v_loc id None) b in
        ctx, b

    (* side-effects *)
    | RE_action {action_stmts = (stmts, retexp); _} ->
        (* Disallow actions at non-byte-aligned locations.  Actions
           can modify the view, which could leave the bitmode of the
           view for the next rule element in an undefined state.
           The tradeoff is that view enquiry cannot be done at
           non-aligned positions.  We could reconsider this if we
           could distinguish view-read-only from view-write
           actions. *)
        let ctx, b = exit_bitmode ctx b loc in
        (* Save and restore free vars around lowering `stmts`, since
           the free variables in the expression language are not
           visible in the grammar language. *)
        let fvs = ctx.ctx_free_vars in
        let astm, ctx = norm_stms ctx stmts in
        let ctx = {ctx with ctx_free_vars = fvs} in
        let act = L_action astm in
        let b =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_l2b act typ loc id None) b in
        (match retexp, ret with
           | None, None ->
               ctx, b
           | None, Some v ->
               assert (is_unit typ);
               let lit_unit = make_av (AV_lit PL_unit) unit loc in
               let lit_unit = ae_of_av lit_unit in
               let assign = L_assign (v, lit_unit) in
               let id = ctx.ctx_id_gen () in
               ctx, add_instr (mk_l2b assign unit loc id None) b
           | Some _, None ->
               (* Consider it an error if the user is not binding the
                  return expression *)
               raise (Error (loc, Unbound_return_expr))
           | Some e, Some v ->
               let ec = to_exp_ctx ctx in
               let ae, ec = Anf_gen.normalize_exp ec e in
               let ctx = of_exp_ctx ctx ec in
               let assign = L_assign (v, ae) in
               let id = ctx.ctx_id_gen () in
               let bi = mk_l2b assign ae.aexp_typ ae.aexp_loc id None in
               ctx, add_instr bi b)

    (* control flow *)
    | RE_constraint c ->
        (* [[RE_constraint c]] = [ v' := [[c]]
                                   if v' [] [ fail ]
                                 ]
           [[v=(RE_constraint c)]] = [ v := [[c]]
                                       if v [] [ fail ]
                                     ]
         *)
        (* Due to the control-flow introduced by a constraint, the
           view should be in a well-defined state at the branch
           targets, otherwise the parser may or may not be in
           bitmode.  The tradeoff is that constraints cannot be
           checked at non-byte-aligned positions. *)
        let ctx, b = exit_bitmode ctx b loc in
        let ac, ctx = norm_exp ctx c in
        (* if we don't have a return variable, generate one to hold
           the value of the constraint *)
        let cvar, ctx, instr = match ret with
            | None ->
                let cvar, ctx = fresh_var ctx typ loc in
                cvar, ctx, L_assign (cvar, ac)
            | Some v ->
                v, ctx, L_assign (v, ac) in
        let b =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_l2b instr typ loc id None) b in
        let ifb = seal_block init_block in
        let elseb, ctx =
          let id = ctx.ctx_id_gen () in
          let s, ctx  = mk_site ctx SS_cond loc in
          add_instr (mk_binst B_fail loc id (Some s)) init_block,
          ctx in
        let elseb = seal_block elseb in
        let cblock = C_if (cvar, ifb, elseb) in
        let id = ctx.ctx_id_gen () in
        ctx, add_instr (mk_c2b cblock loc id None) b

    (* since the case when there is no return value is especially
       simple, handle it separately *)
    | RE_seq res when ret = None ->
        (* [[RE_seq res]] = [ {[[re_i]] | re_i <- res} ] *)
        let ctx, b = exit_bitmode ctx b loc in
        (* Save and restore free vars across combinator. *)
        let fvs = ctx.ctx_free_vars in
        let ctx, b = List.fold_left (fun (ctx, b) re ->
                         lower_rule_elem trace ctx m b ret re
                       ) (ctx, b) res in
        {ctx with ctx_free_vars = fvs}, b

    (* with a return value, the outline is the same as above, but we
       have to ensure that the return variable is properly assigned *)
    | RE_seq res ->
        (* [[v=(RE_seq res)]] = [ {v_i := [[re_i]] | re_i <- res}
                                  v := [v_i | i]
                                ]
         *)
        let ctx, b = exit_bitmode ctx b loc in
        (* Save and restore free vars across combinator. *)
        let fvs = ctx.ctx_free_vars in
        let ctx, b, vs =
          List.fold_left (fun (ctx, b, vs) (re: TypedAst.rule_elem) ->
              (* create variables for the elements of the sequence *)
              let v, ctx =
                fresh_var ctx re.rule_elem_aux  re.rule_elem_loc in
              let ret = Some v in
              let ctx, b = lower_rule_elem trace ctx m b ret re in
              ctx, b, v :: vs
            ) (ctx, b, []) res in
        let ctx = {ctx with ctx_free_vars = fvs} in
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
        let v = match ret with
            | None   -> assert false (* handled above *)
            | Some v -> v in
        let assign = L_assign (v, l) in
        let b =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_l2b assign typ loc id None) b in
        ctx, b

    (* there is no special case for ret since it gets handled by
       whichever re succeeds *)
    | RE_choice res ->
        let loc_fn (re: TypedAst.rule_elem) =
          re.rule_elem_loc in
        let lower_fn (ctx: context) (b: block) (c: TypedAst.rule_elem) =
          lower_rule_elem trace ctx m b ret c in
        lower_choices loc ctx b res loc_fn lower_fn

    | RE_star (re', None) when ret = None ->
        (* [[RE_star re]] = do [ loop [ [[re]] ]
                            handle Succ []
         *)

        (* This is a special case of the next clause (ret <> None),
           but treated separately for simplicity. *)
        let ctx, b = exit_bitmode ctx b loc in
        (* Save and restore free vars across combinator. *)
        let fvs = ctx.ctx_free_vars in
        (* This turns into a `simple' infinite loop wrapped in a
           do block with a handler that ignores a failure. *)
        let ctx, b' = lower_rule_elem trace ctx m init_block ret re' in
        let ctx = {ctx with ctx_free_vars = fvs} in
        let loop = C_loop (true, seal_block b') in
        let b' =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_c2b loop loc id None) init_block in
        let b' = seal_block b' in
        let fail = seal_handler init_block in
        let doblock = C_do (b', (H_success, fail)) in
        let b =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_c2b doblock loc id None) b in
        ctx, b

    | RE_star (re', None) ->
        (* [[v=(RE_star re)]] = [ v := []
                                  do [ loop [ [[v'=(re)]]
                                              v := v' :: v
                                            ]]
                                  handle Succ [ v := List.rev v ]
                                ]
         *)

        let ctx, b = exit_bitmode ctx b loc in
        (* Collect the matches generated by the loop over `re'` into a
           list, and wrap with a handler that ignores failure and
           binds the reversed list to the return var. *)
        let vr, ctx = get_ret_var ctx ret in
        (* Initialize vr to []. *)
        let null = ae_of_av (constr_av "[]" "[]" [] typ loc) in
        let assign =
          let id = ctx.ctx_id_gen () in
          mk_l2b (L_assign (vr, null)) typ loc id None in
        let b = add_instr assign b in
        (* Create the block for `re'`. *)
        let b' = init_block in
        let v', ctx = fresh_var ctx re'.rule_elem_aux re'.rule_elem_loc in
        let ret' = Some v' in
        (* Save and restore free vars across combinator. *)
        let fvs = ctx.ctx_free_vars in
        let ctx, b' = lower_rule_elem trace ctx m b' ret' re' in
        let ctx = {ctx with ctx_free_vars = fvs} in
        (* Update the return value: `vr := v' :: vr`. *)
        let l = constr_av "[]" "::" [av_of_var v';
                                     av_of_var vr] typ loc in
        let id = ctx.ctx_id_gen () in
        let li = L_assign (vr, ae_of_av l) in
        let assign = mk_l2b li typ loc id None in
        let b' = add_instr assign b' in
        (* Embed this in a loop for `re'*`. *)
        let loop = C_loop (true, seal_block b') in
        let id = ctx.ctx_id_gen () in
        let b' = add_instr (mk_c2b loop loc id None) init_block in
        let b' = seal_block b' in
        (* Reverse the list in the handler: `vr := List.rev vr`. *)
        let ftyp = mk_func_type ctx typ typ in
        let f = mk_mod_func "List" "rev" ftyp loc in
        let l = make_ae (AE_apply (f, [av_of_var vr])) typ loc None in
        let id = ctx.ctx_id_gen () in
        let assign = mk_linst (L_assign (vr, l)) typ loc id None in
        let fail = add_instr assign init_block in
        let fail = seal_handler fail in
        (* Create a `do` block that ignores the failure. *)
        let doblock = C_do (b', (H_success, fail)) in
        let b =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_c2b doblock loc id None) b in
        ctx, b

    | RE_star (re', Some e) ->
        (* [[RE_star (re, e)]] = [ n := [[e]]
                                   loop [ c := n > 0
                                          if c [] [break]
                                          [[re]]
                                          n := n - 1 ]
                                 ]
           [[v=(RE_star (re, e))]] = [ v := []
                                       n := [[e]]
                                       loop [ c := n > 0
                                              if c [] [break]
                                              [[v'=(re)]]
                                              v := v' :: v
                                              n := n - 1 ]
                                       v := List.rev v
                                     ]
         *)

        let ctx, b = exit_bitmode ctx b loc in
        (* The loop bound `e` is tracked in a variable.  Note a big
           difference wrt RE_star (_, None): `re'*` can never fail, but
           `re'^e` can fail. *)
        (* Collect the matches generated by the loop over `re'` into a
           list, and wrap with a handler that ignores failure and
           binds the reversed list to the return var (if we have one). *)
        let have_ret = ret <> None in
        (* Initialize vr to [] *)
        let vr, ctx = get_ret_var ctx ret in
        let null = ae_of_av (constr_av "[]" "[]" [] typ loc) in
        let b = if   have_ret
                then let id = ctx.ctx_id_gen () in
                     let li = L_assign (vr, null) in
                     add_instr (mk_l2b li typ loc id None) b
                else b in
        let bnd, ctx = norm_exp ctx e in
        (* Assign the bound `bnd` to a variable `n`, and then decrement
           `n` in a loop as `re'` is matched.  The loop terminates
           when the `n` fails the constraint that it is positive. *)
        let n, ctx = fresh_var ctx e.expr_aux e.expr_loc in
        let id = ctx.ctx_id_gen () in
        let li = L_assign (n, bnd) in
        let assign = mk_l2b li e.expr_aux e.expr_loc id None in
        let b = add_instr assign b in
        (* Build the loop block. *)
        let b' = init_block in
        (* Evaluate the conditional: `c := n > 0`. *)
        let z = av_of_int ctx 0 Ast.usize_t e.expr_loc in
        let ae = AE_binop (Ast.Gt Ast.usize_t, av_of_var n, z) in
        let ae = make_ae ae bool e.expr_loc None in
        let c, ctx = fresh_var ctx bool e.expr_loc in
        let id = ctx.ctx_id_gen () in
        let li = L_assign (c, ae) in
        let assign = mk_l2b li bool e.expr_loc id None in
        let b' = add_instr assign b' in
        (* Check the conditional in an `if` block: `if c [] [break]` *)
        let thenb = seal_block init_block in
        let elseb, ctx =
          let id = ctx.ctx_id_gen () in
          let bi = B_break in
          let s, ctx  = mk_site ctx SS_break e.expr_loc in
          add_instr (mk_binst bi loc id (Some s)) init_block,
          ctx in
        let elseb = seal_block elseb in
        (* Add the `if` check *)
        let ifb, ctx =
          let id = ctx.ctx_id_gen () in
          let s, ctx  = mk_site ctx SS_cond loc in
          let ci = C_if (c, thenb, elseb) in
          mk_c2b ci e.expr_loc id (Some s), ctx in
        let b' = add_instr ifb b' in
        (* Match `re'` binding the result to `v'`. *)
        let v', ctx = fresh_var ctx re'.rule_elem_aux re'.rule_elem_loc in
        let ret' = if have_ret then Some v' else None in
        (* Save and restore free vars across combinator. *)
        let fvs = ctx.ctx_free_vars in
        let ctx, b' = lower_rule_elem trace ctx m b' ret' re' in
        let ctx = {ctx with ctx_free_vars = fvs} in
        let b' = if   have_ret
                 then (* Update the return value: `vr := v' :: vr`. *)
                   let l = constr_av "[]" "::" [av_of_var v';
                                                av_of_var vr] typ loc in
                   let id = ctx.ctx_id_gen () in
                   let assign =
                     let li = L_assign (vr, ae_of_av l) in
                     mk_l2b li typ loc id None in
                   add_instr assign b'
                 else  b' in
        (* `n := n - 1` *)
        let o = av_of_int ctx 1 Ast.usize_t e.expr_loc in
        let ae = AE_binop (Ast.Minus Ast.usize_t, av_of_var n, o) in
        let ae = make_ae ae usize e.expr_loc None in
        let id = ctx.ctx_id_gen () in
        let li = L_assign (n, ae) in
        let assign = mk_l2b li e.expr_aux e.expr_loc id None in
        let b' = add_instr assign b' in
        (* The loop block is done. *)
        let id = ctx.ctx_id_gen () in
        let ci = C_loop (false, seal_block b') in
        let loop = mk_c2b ci loc id None in
        let b = add_instr loop b in
        let b =
          if   have_ret
          then (* Reorder the accumulated matches: `vr := List.rev vr`. *)
            let ftyp = mk_func_type ctx typ typ in
            let f = mk_mod_func "List" "rev" ftyp loc in
            let l =
              make_ae (AE_apply (f, [av_of_var vr])) typ loc None in
            let id = ctx.ctx_id_gen () in
            let li = L_assign (vr, l) in
            let assign = mk_l2b li typ loc id None in
            add_instr assign b
          else  b in
        ctx, b

    | RE_opt re' when ret == None ->
        (* [[RE_opt re]] = [ do [ [[re]] ]
                             handle Succ []
                           ]
         *)

        (* Optional bit-elements complicate bit-alignment
           calculations, so they are currently forbidden in
           bit-mode. *)
        let ctx, b = exit_bitmode ctx b loc in
        (* Save and restore free vars across combinator. *)
        let fvs = ctx.ctx_free_vars in
        (* Create a block for `do` in which to match `re'`. *)
        let ctx, b' =
          lower_rule_elem trace ctx m init_block ret re' in
        let ctx = {ctx with ctx_free_vars = fvs} in
        let fail = seal_handler init_block in
        (* Create a `do` block that ignores the failure. *)
        let doblock = C_do (seal_block b', (H_success, fail)) in
        let b =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_c2b doblock loc id None) b in
        ctx, b

    | RE_opt re' ->
        (* [[v=(RE_opt re)]] = [ do [ [[v'=(re)]]
                                      v := Some v' ]
                                 handle Succ [ v := None ]
                               ]
         *)
        (* Optional bit-elements complicate bit-alignment
           calculations, so they are currently forbidden in
           bit-mode. *)
        let ctx, b = exit_bitmode ctx b loc in
        let vr, ctx = get_ret_var ctx ret in
        (* Create a variable `v'` to bind the match for `re'`. *)
        let v', ctx =
          fresh_var ctx re'.rule_elem_aux re'.rule_elem_loc in
        let ret' = Some v' in
        (* Save and restore free vars across combinator. *)
        let fvs = ctx.ctx_free_vars in
        let ctx, b' =
          lower_rule_elem trace ctx m init_block ret' re' in
        let ctx = {ctx with ctx_free_vars = fvs} in
        (* In success path: `vr := option::Some(v')` *)
        let av = constr_av "option" "Some" [av_of_var v'] typ loc in
        let id = ctx.ctx_id_gen () in
        let li = L_assign (vr, ae_of_av av) in
        let assign = mk_l2b li typ loc id None in
        let b' = add_instr assign b' in
        (* In failure path: `vr := option::None()` *)
        let fail = init_block in
        let none = constr_av "option" "None" [] typ loc in
        let id = ctx.ctx_id_gen () in
        let li = L_assign (vr, ae_of_av none) in
        let assign = mk_linst li typ loc id None in
        let fail = add_instr assign fail in
        let fail = seal_handler fail in
        (* Create a `do` block that ignores the failure. *)
        let doblock = C_do (seal_block b', (H_success, fail)) in
        let b =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_c2b doblock loc id None) b in
        ctx, b

    | RE_epsilon ->
        ctx, b

    (* suspend/resume elements *)

    | RE_suspend_resume (n, args)
         when Location.value n = "require_remaining"
              && List.length args = 2 ->
        let vu = List.nth args 0 in
        let e  = List.nth args 1 in
        let ctx, b = exit_bitmode ctx b loc in
        (* compute the suspension condition *)
        let ae, ctx = norm_exp ctx e in
        let ve, ctx = fresh_var ctx e.expr_aux e.expr_loc in
        let assign =
          let id = ctx.ctx_id_gen () in
          let li = L_assign (ve, ae) in
          mk_l2b li e.expr_aux e.expr_loc id None in
        let b = add_instr assign b in
        let avu, ctx = norm_exp ctx vu in
        let vvu, ctx = fresh_var ctx vu.expr_aux vu.expr_loc in
        let assign =
          let id = ctx.ctx_id_gen () in
          let li = L_assign (vvu, avu) in
          mk_l2b li vu.expr_aux vu.expr_loc id None in
        let b = add_instr assign b in
        let susp, ctx =
          let id = ctx.ctx_id_gen () in
          let bi = B_require_remaining (vvu, ve) in
          let s, ctx  = mk_site ctx SS_dynamic loc in
          mk_binst bi loc id (Some s), ctx in
        let b = add_instr susp b in
        ctx, b

    | RE_suspend_resume _ ->
        (* Other cases should have been forbidden by the type-checker. *)
        assert false

    (* view control *)

    | RE_set_view e ->
        (* [[RE_set_view e]] = [ v' := [[e]]
                                 set-view v'
                               ]
           [[v=(RE_set_view e)]] = [ v' := [[e]]
                                     set-view v'
                                     v := ()
                                   ]
         *)
        let ctx, b = exit_bitmode ctx b loc in
        let ae, ctx = norm_exp ctx e in
        let v, ctx = fresh_var ctx e.expr_aux e.expr_loc in
        let assign =
          let id = ctx.ctx_id_gen () in
          let li = L_assign (v, ae) in
          mk_l2b li e.expr_aux e.expr_loc id None in
        let b = add_instr assign b in
        let b, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_set_view v in
          let s, ctx  = mk_site ctx SS_view loc in
          add_instr (mk_l2b li unit loc id (Some s)) b,
          ctx in
        (* Any return binding should be set to `() : unit`. *)
        let b = match ret with
            | None   -> b
            | Some v ->
                let lit_unit = ae_of_av (make_av (AV_lit PL_unit) unit loc) in
                let assign =
                  let id = ctx.ctx_id_gen () in
                  let li = L_assign (v, lit_unit) in
                  mk_l2b li unit loc id None in
                add_instr assign b in
        ctx, b

    (* Due to _set_view, variable state restoration after a
       failure is decoupled from view restoration.  So views need to
       be restored explicitly after failures, unlike variable state. *)
    | RE_at_pos (e, re') ->
        (* [[v=?(RE_at_pos (e, re))]] = [ v' := [[e]]
                                          do [ push_view
                                               set_pos v'
                                               [[v=?(re)]]
                                               pop_view ]
                                          handle Fail [ pop_view ]
                                        ]
         *)
        let ctx, b = exit_bitmode ctx b loc in
        (* Evaluate the position `e` into `v`. *)
        let ae, ctx = norm_exp ctx e in
        let v, ctx = fresh_var ctx e.expr_aux e.expr_loc in
        let assign =
          let id = ctx.ctx_id_gen () in
          let li = L_assign (v, ae) in
          mk_l2b li e.expr_aux e.expr_loc id None in
        let b = add_instr assign b in
        (* Wrap the match for `re'` in a `do` block. *)
        let b' = init_block in
        (* Save the current view before the excursion. *)
        let b' =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_l2b L_push_view unit loc id None) b' in
        (* Set the new view.  The old view needs to be restored on
           both the success and failure paths. *)
        let set_pos, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_set_pos v in
          let s, ctx  = mk_site ctx SS_view re'.rule_elem_loc in
          mk_l2b li unit loc id (Some s), ctx in
        let b' = add_instr set_pos b' in
        (* Save and restore free vars across combinator. *)
        let fvs = ctx.ctx_free_vars in
        (* Perform the match for `re'`. *)
        let ctx, b' = lower_rule_elem trace ctx m b' ret re' in
        let ctx = {ctx with ctx_free_vars = fvs} in
        (* Restore the view after a successful match. *)
        let b', ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_pop_view in
          let s, ctx  = mk_site ctx SS_view re'.rule_elem_loc in
          add_instr (mk_l2b li unit loc id (Some s)) b',
          ctx in
        (* The do block is done.  The handler needs to restore the
           view in the failure path. *)
        let fail, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_pop_view  in
          let s, ctx  = mk_site ctx SS_view loc in
          add_instr (mk_linst li unit loc id (Some s)) init_block,
          ctx in
        let fail = seal_handler fail in
        let doblock = C_do (seal_block b', (H_failure, fail)) in
        let b =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_c2b doblock loc id None) b in
        ctx, b

    | RE_at_view (e, re') ->
        (* [[v=?(RE_at_view (e, re))]] = [ v' := [[e]]
                                           do [ push_view
                                                set_view v'
                                                [[v=?(re)]]
                                                pop_view ]
                                           handle Fail [ pop_view ]
                                         ]
         *)
        let ctx, b = exit_bitmode ctx b loc in
        (* Essentially the same as above, but with L_set_view. *)
        (* Evaluate the view `e` into `v`. *)
        let ae, ctx = norm_exp ctx e in
        let v, ctx = fresh_var ctx e.expr_aux e.expr_loc in
        let assign =
          let id = ctx.ctx_id_gen () in
          let li = L_assign (v, ae) in
          mk_l2b li e.expr_aux e.expr_loc id None in
        let b = add_instr assign b in
        (* Wrap the match for `re'` in a `do` block. *)
        let b' = init_block in
        (* Save the current view before the excursion. *)
        let b' =
          let id = ctx.ctx_id_gen () in
          let li = L_push_view in
          add_instr (mk_l2b li unit loc id None) b' in
        (* Set the new view.  The old view needs to be restored on
           both the success and failure paths. *)
        let set_pos, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_set_view v in
          let s, ctx  = mk_site ctx SS_view re'.rule_elem_loc in
          mk_l2b li unit loc id (Some s), ctx in
        let b' = add_instr set_pos b' in
        (* Save and restore free vars across combinator. *)
        let fvs = ctx.ctx_free_vars in
        (* Perform the match for `re'`. *)
        let ctx, b' = lower_rule_elem trace ctx m b' ret re' in
        let ctx = {ctx with ctx_free_vars = fvs} in
        (* Restore the view after a successful match. *)
        let b', ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_pop_view in
          let s, ctx  = mk_site ctx SS_view re'.rule_elem_loc in
          add_instr (mk_l2b li unit loc id (Some s)) b',
          ctx in
        (* The do block is done.  The handler needs to restore the
           view in the failure path. *)
        let fail, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_pop_view in
          let s, ctx  = mk_site ctx SS_view loc in
          add_instr (mk_linst li unit loc id (Some s)) init_block,
          ctx in
        let fail = seal_handler fail in
        let doblock = C_do (seal_block b', (H_failure, fail)) in
        let b =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_c2b doblock loc id None) b in
        ctx, b

    (* handle the multi-assignment map-view case before the more
       general map-view case below *)
    | RE_map_views (e, ({rule_elem = RE_non_term (m, nt, Some args); _}
                        as re'))
         when List.exists (fun (_, a, _) -> a = Ast.A_in) args ->
        (* [[vr=(RE_map_views (e, NT<i <- as, j=a>))]] =
              [ vs := [[e]
                is := [[as]] ...
                jc := [[a]]
                do [ vr := [] (* Allocate here to make it more local *)
                     push_view
                     loop [ c  := vs == []
                            ci := is == [] ...
                            c  := c || ci ...
                            if c [break] []
                            (* Adjust tails along with extracting
                               heads for code-gen simplicity.  But
                               execution would be more efficient if
                               tails were updated after the match. *)
                            v  := List.head vs
                            vs := List.tail vs
                            i  := List.head is
                            is := List.tail is ...
                            set_view v
                            [[r=(NT<i=i, ..., j=jc, ...>)]]
                            vr := r :: vr ]
                     vr := List.rev vr
                     pop_view ]
                handle Fail [ pop_view ]
              ]
         *)
        let ctx, b = exit_bitmode ctx b loc in
        let have_ret = ret <> None in
        let ae, ctx = norm_exp ctx e in
        let vs, ctx = fresh_var ctx e.expr_aux e.expr_loc in
        let assign =
          let id = ctx.ctx_id_gen () in
          let li = L_assign (vs, ae) in
          mk_l2b li e.expr_aux e.expr_loc id None in
        let b = add_instr assign b in
        (* Split args into their types: iters are the variables
           holding the lists to be looped over (i.e. the condition
           variables), while consts are the variables holding values
           that don't change in the loop.  Note that `vs` holding the
           list of views is also a condition variable. *)
        let b, ctx, iters, consts =
          List.fold_left (fun (b, ctx, is, cs) (i, a, e) ->
              let ae, ctx = norm_exp ctx e in
              (* allocate a variable for this value *)
              let e_typ, e_loc = e.expr_aux, e.expr_loc in
              let v, ctx = fresh_var ctx e_typ e_loc in
              let id = ctx.ctx_id_gen () in
              let li = L_assign (v, ae) in
              let assign = mk_l2b li e_typ e_loc id None in
              let b = add_instr assign b in
              let is, cs = match a with
                  | Ast.A_in -> (i, v) :: is, cs
                  | Ast.A_eq -> is, (i, v) :: cs in
              b, ctx, is, cs
            ) (b, ctx, [], []) args in
        (* Wrap the excursions over `vs` in a handled `do` block. *)
        let db = init_block in
        (* Initialize the return value `vr` if any. *)
        let vr, ctx = get_ret_var ctx ret in
        let null = ae_of_av (constr_av "[]" "[]" [] typ loc) in
        let db =
          if   have_ret
          then let id = ctx.ctx_id_gen () in
               let li = L_assign (vr, null) in
               add_instr (mk_l2b li typ loc id None) db
          else db in
        (* Save the current view before the excursion. *)
        let db =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_l2b L_push_view unit loc id None) db in
        (* Create the loop block to loop over `vs`. *)
        let lb = init_block in
        (* Create a condition variable to evaluate the loop exit
           condition:
           `c := vs == [] && is == [] forall i`. *)
        let null = constr_av "[]" "[]" [] e.expr_aux e.expr_loc in
        let ae = AE_binop (Ast.Eq, (av_of_var vs), null) in
        let ae = make_ae ae bool e.expr_loc None in
        let c, ctx = fresh_var ctx bool e.expr_loc in
        (* tmp for `iters` loop *)
        let ct, ctx = fresh_var ctx bool e.expr_loc in
        (* `c := cs == []` *)
        let assign =
          let id = ctx.ctx_id_gen () in
          let li = L_assign (c, ae) in
          mk_l2b li bool e.expr_loc id None in
        let lb = add_instr assign lb in
        let lb =
          List.fold_left (fun lb (_i, v) ->
              (* Compute the logical `or` of `c` with `v == []` for
                 each list `v` in `iters`. *)
              (* `ct := v == []` *)
              let null = constr_av "[]" "[]" [] v.v_typ v.v_loc in
              let ae = AE_binop (Ast.Eq, (av_of_var v), null) in
              let ae = make_ae ae bool v.v_loc None in
              let id = ctx.ctx_id_gen () in
              let li = L_assign (ct, ae) in
              let assign = mk_l2b li bool v.v_loc id None in
              let lb = add_instr assign lb in
              (* `c := c || ct` *)
              let ae =
                AE_binop (Ast.Lor, (av_of_var c), (av_of_var ct)) in
              let ae = make_ae ae bool c.v_loc None in
              let id = ctx.ctx_id_gen () in
              let li = L_assign (c, ae) in
              let assign = mk_l2b li bool c.v_loc id None in
              add_instr assign lb
            ) lb iters in
        (* Check for loop exit condition; i.e. if `c` is true. *)
        let thenb, ctx =
          let id = ctx.ctx_id_gen () in
          let s, ctx  = mk_site ctx SS_break e.expr_loc in
          add_instr (mk_binst B_break loc id (Some s)) init_block,
          ctx in
        let thenb = seal_block thenb in
        let elseb = seal_block init_block in
        let ifb, ctx =
          let id  = ctx.ctx_id_gen () in
          let ci  = C_if (c, thenb, elseb) in
          let s, ctx   = mk_site ctx SS_cond e.expr_loc in
          mk_c2b ci e.expr_loc id (Some s), ctx in
        let lb  = add_instr ifb lb in
        (* Extract the heads of the various lists, and update the
           lists in the condition variables to their tails.  Collect
           the variables storing the heads in the same order as `vs`
           to make the call to the non-terminal *)
        let ctx, lb, ls =
          List.fold_left (fun (ctx, lb, ls) is ->
              (* Get the head element: `i := List.head is`. *)
              (* Use the _element type_ of the list type
                 in `is.v_typ` where appropriate below, required for
                 data-layout. *)
              let elmtyp = list_elem is.v_typ in
              let ftyp = mk_func_type ctx is.v_typ elmtyp in
              let f = mk_mod_func "List" "head" ftyp is.v_loc in
              let hd = make_ae (AE_apply (f, [av_of_var vs]))
                         elmtyp is.v_loc None in
              let i, ctx = fresh_var ctx elmtyp e.expr_loc in
              let assign =
                let id = ctx.ctx_id_gen () in
                let li = L_assign (i, hd) in
                mk_l2b li elmtyp is.v_loc id None in
              let lb = add_instr assign lb in
              (* update the list: `is := List.tail is` *)
              let ftyp = mk_func_type ctx is.v_typ is.v_typ in
              let f  = mk_mod_func "List" "tail" ftyp is.v_loc in
              let tl = make_ae (AE_apply (f, [av_of_var is]))
                         is.v_typ is.v_loc None in
              let assign =
                let id = ctx.ctx_id_gen () in
                let li = L_assign (is, tl) in
                mk_l2b li is.v_typ is.v_loc id None in
              let lb = add_instr assign lb in
              ctx, lb, i :: ls
            ) (ctx, lb, []) (vs :: List.map snd iters) in
        let ls = List.rev ls in (* make the order match the input *)
        let v, is = List.hd ls, List.tl ls in
        (* `v` now contains the view to set, and `is` holds the
           view-specific values of the attributes in `iters`. *)
        let is = List.combine iters is in
        (* Set the view: set_view v *)
        let lb, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_set_view v in
          let s, ctx  = mk_site ctx SS_view v.v_loc in
          add_instr (mk_l2b li unit v.v_loc id (Some s)) lb,
          ctx in
        (* Construct the inherited attr argument list for the call. *)
        let iters' = List.map (fun ((i, _), v) -> (i, v)) is in
        let args' = iters' @ consts in
        let m = Anf_common.modul_of_mname m in
        let loc' = re'.rule_elem_loc in
        let r, ctx = fresh_var ctx re'.rule_elem_aux loc'  in
        let call, ctx =
          let id = ctx.ctx_id_gen () in
          let bi = B_call_nonterm (m, nt, args', r) in
          let s, ctx  = mk_site ctx SS_call (Location.loc nt) in
          mk_binst bi loc' id (Some s), ctx in
        let lb = add_instr call lb in
        let lb =
          if   have_ret
          then (* Accumulate the return value: `vr := r :: vr`. *)
            let l = constr_av "[]" "::" [av_of_var r;
                                         av_of_var vr] typ loc in
            let assign =
              let id = ctx.ctx_id_gen () in
              let li = L_assign (vr, ae_of_av l) in
              mk_l2b li typ loc id None in
            add_instr assign lb
          else  lb in
        (* The loop block is done; create the loop instruction. *)
        let loop = C_loop (false, seal_block lb) in
        let db =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_c2b loop loc id None) db in
        let db =
          if   have_ret
          then (* Reverse the result list: `vr := List.rev vr` *)
            let ftyp = mk_func_type ctx typ typ in
            let f = mk_mod_func "List" "rev" ftyp loc in
            let l =
              make_ae (AE_apply (f, [av_of_var vr])) typ loc None in
            let id = ctx.ctx_id_gen () in
            let li = L_assign (vr, l) in
            let assign = mk_l2b li typ loc id None in
            add_instr assign db
          else db in
        (* Restore the saved view. *)
        let db, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_pop_view in
          let s, ctx  = mk_site ctx SS_view loc in
          add_instr (mk_l2b li unit loc id (Some s)) db,
          ctx in
        (* Restore it in the `do` handler. *)
        let fail, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_pop_view in
          let s, ctx  = mk_site ctx SS_view loc in
          add_instr (mk_linst li unit loc id (Some s)) init_block,
          ctx in
        let fail = seal_handler fail in
        let dob = C_do (seal_block db, (H_failure, fail)) in
        let b =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_c2b dob loc id None) b in
        ctx, b

    | RE_map_views (e, re') ->
        (* [[vr=(RE_map_views (e, re))]] =
              [ vs := [[e]]
                do [ vr := [] (* Allocate here to make it more local *)
                     push_view
                     loop [ c := vs == []
                            if c [break] []
                            v := List.head vs
                            set_view v
                            [[r=(re)]]
                            vr := r :: vr
                            vs := List.tail vs
                          ]
                     vr := List.rev vr
                     pop_view ]
                handle Fail [ pop_view ]
              ]
         *)
        let ctx, b = exit_bitmode ctx b loc in
        let have_ret = ret <> None in
        (* Evaluate the views `e` into `vs`. *)
        let ae, ctx = norm_exp ctx e in
        let vs, ctx = fresh_var ctx e.expr_aux e.expr_loc in
        let assign =
          let id = ctx.ctx_id_gen () in
          let li = L_assign (vs, ae) in
          mk_l2b li e.expr_aux e.expr_loc id None in
        let b = add_instr assign b in
        (* Wrap the excursions over `vs` in a handled `do` block. *)
        let db = init_block in
        (* Initialize vr to [] if needed. *)
        let vr, ctx = get_ret_var ctx ret in
        let null = ae_of_av (constr_av "[]" "[]" [] typ loc) in
        let db =
          if   have_ret
          then let id = ctx.ctx_id_gen () in
               let li = L_assign (vr, null) in
               add_instr (mk_l2b li typ loc id None) db
          else db in
        (* Save the current view before the excursion. *)
        let db, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_push_view in
          let s, ctx  = mk_site ctx SS_view re'.rule_elem_loc in
          add_instr (mk_l2b li unit loc id (Some s)) db,
          ctx in
        (* Create the loop block to loop over `vs`. *)
        let lb = init_block in
        (* Evaluate the loop exit condition `c := vs == []`. *)
        let null = constr_av "[]" "[]" [] e.expr_aux e.expr_loc in
        let ae = AE_binop (Ast.Eq, (av_of_var vs), null) in
        let ae = make_ae ae bool e.expr_loc None in
        let c, ctx = fresh_var ctx bool e.expr_loc in
        let assign =
          let id = ctx.ctx_id_gen () in
          let li = L_assign (c, ae) in
          mk_l2b li bool e.expr_loc id None in
        let lb = add_instr assign lb in
        (* Check for loop exit condition. *)
        let thenb, ctx =
          let id = ctx.ctx_id_gen () in
          let bi = B_break in
          let s, ctx  = mk_site ctx SS_break e.expr_loc in
          add_instr (mk_binst bi loc id (Some s)) init_block,
          ctx in
        let thenb = seal_block thenb in
        let elseb = seal_block init_block in
        let ifb, ctx   =
          let id = ctx.ctx_id_gen () in
          let ci = C_if (c, thenb, elseb) in
          let s, ctx  = mk_site ctx SS_cond e.expr_loc in
          mk_c2b ci e.expr_loc id (Some s), ctx in
        let lb = add_instr ifb lb in
        (* Get the head view to set: `v := List.head vs`. *)
        (* Use the _element type_ of the list type in `e.expr_aux`
           where appropriate below, required for data-layout. *)
        let elmtyp = list_elem e.expr_aux in
        let ftyp = mk_func_type ctx e.expr_aux elmtyp in
        let f = mk_mod_func "List" "head" ftyp e.expr_loc in
        let hd = make_ae (AE_apply (f, [av_of_var vs]))
                   elmtyp e.expr_loc None in
        let v, ctx = fresh_var ctx elmtyp e.expr_loc in
        let assign =
          let id = ctx.ctx_id_gen () in
          let li = L_assign (v, hd) in
          mk_l2b li elmtyp e.expr_loc id None in
        let lb = add_instr assign lb in
        (* Set this view. *)
        let lb, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_set_view v in
          let s, ctx  = mk_site ctx SS_view e.expr_loc in
          add_instr (mk_l2b li unit e.expr_loc id (Some s)) lb,
          ctx in
        (* Bind the match for `re'` into `r`. *)
        let r, ctx =
          fresh_var ctx re'.rule_elem_aux re'.rule_elem_loc in
        let ret' = if have_ret then Some r else None in
        (* Save and restore free vars across combinator. *)
        let fvs = ctx.ctx_free_vars in
        let ctx, lb = lower_rule_elem trace ctx m lb ret' re' in
        let ctx = {ctx with ctx_free_vars = fvs} in
        let lb =
          if   have_ret
          then (* Add the result to `vr`: `vr := r :: vr`. *)
            let l = constr_av "[]" "::" [av_of_var r;
                                         av_of_var vr] typ loc in
            let assign =
              let id = ctx.ctx_id_gen () in
              let li = L_assign (vr, ae_of_av l) in
              mk_l2b li typ loc id None in
            add_instr assign lb
          else lb in
        (* Update the remaining views: `vs := List.tail vs`. *)
        let f = mk_mod_func "List" "tail" ftyp e.expr_loc in
        let tl = make_ae (AE_apply (f, [av_of_var vs]))
                   e.expr_aux e.expr_loc None in
        let assign =
          let id = ctx.ctx_id_gen () in
          let li = L_assign (vs, tl) in
          mk_l2b li e.expr_aux e.expr_loc id None in
        let lb = add_instr assign lb in
        (* The loop block is done; create the loop instruction. *)
        let loop = C_loop (false, seal_block lb) in
        let db =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_c2b loop loc id None) db in
        let db =
          if   have_ret
          then (* Reverse the result list: `vr := List.rev vr` *)
            let ftyp = mk_func_type ctx typ typ in
            let f = mk_mod_func "List" "rev" ftyp loc in
            let l = make_ae (AE_apply (f, [av_of_var vr]))
                      typ loc None in
            let id = ctx.ctx_id_gen () in
            let li = L_assign (vr, l) in
            let assign = mk_l2b li typ loc id None in
            add_instr assign db
          else db in
        (* Restore the saved view. *)
        let db, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_pop_view in
          let s, ctx  = mk_site ctx SS_view e.expr_loc in
          add_instr (mk_l2b li unit loc id (Some s)) db,
          ctx in
        (* Restore it in the `do` handler. *)
        let fail, ctx =
          let id = ctx.ctx_id_gen () in
          let li = L_pop_view in
          let s, ctx  = mk_site ctx SS_view e.expr_loc in
          add_instr (mk_linst li unit loc id (Some s)) init_block,
          ctx in
        let fail = seal_handler fail in
        let dob = C_do (seal_block db, (H_failure, fail)) in
        let b =
          let id = ctx.ctx_id_gen () in
          add_instr (mk_c2b dob loc id None) b in
        ctx, b

(* Unlike a rule element, a rule has no explicit return value, since
   the 'return values' of a rule are assigned by the actions within a
   well-typed rule. *)
let lower_rule (trace: bool) (ctx: context) (m: Ast.mname) (b: block)
      (r: TypedAst.rule)
    : (context * block) =
  (* Initialize the rule temporaries. *)
  let ctx, b =
    List.fold_left (fun (ctx, b) (v, _, (e: TypedAst.exp)) ->
        let v, ctx = bind_var ctx v e.expr_aux in
        let ae, ctx = norm_exp ctx e in
        let assign =
          let id = ctx.ctx_id_gen () in
          let li = L_assign (v, ae) in
          mk_l2b li e.expr_aux e.expr_loc id None in
        ctx, add_instr assign b
      ) (ctx, b) r.rule_temps in
  (* Now lower the rule elements. *)
  let ctx, b =
    List.fold_left (fun (ctx, b) re ->
        lower_rule_elem trace ctx m b None re
      ) (ctx, b) r.rule_rhs in
  (* Ensure bitmode has been exited at the end of the rule. *)
  exit_bitmode ctx b r.rule_loc

(* A non-terminal requires the set up of its attributes and lowering
   of the ordered choice of its rules; in addition, it needs an
   nt_entry so that it can be called from other rules. *)
let lower_general_ntd (trace: bool) (ctx: context) (ntd: TypedAst.non_term_defn)
    : context =
  (* Save and restore free vars across definition. *)
  let fvs = ctx.ctx_free_vars in
  let nt_name = Location.value ntd.non_term_name in
  let mname = Ast.(Modul (Mod_inferred ntd.non_term_mod)) in
  let typ = get_nt_typ ctx mname nt_name in
  let loc = ntd.non_term_loc in
  (* Ensure the NT var is bound in the rules.  If the var was not
     originally present, we should have generated it. *)
  let rv, ctx = match ntd.non_term_varname with
      | None   -> assert false
      | Some v -> bind_var ctx v typ in
  (* And similarly for the inherited attributes *)
  let tenv = ctx.ctx_tenv in
  let nt_inh_attrs, ctx =
    List.fold_left (fun (attrs, ctx) (v, te, _) ->
        let ia = Ast.var_name v in
        (* todo: move this into a convenient util *)
        let te = TypedAstUtils.expand_type_abbrevs tenv te in
        let typ = TypeConv.intern tenv te in
        let v, ctx = bind_var ctx v typ in
        (StringMap.add ia (v, typ) attrs), ctx
      ) (StringMap.empty, ctx) ntd.non_term_inh_attrs in
  (* Create the wrapper functions for `lower_choices`. *)
  let loc_fn (r: TypedAst.rule) = r.rule_loc in
  let lower_fn (ctx: context) (b: block) (c: TypedAst.rule) =
    lower_rule trace ctx mname b c in
  (* Lower the choices into a new block. *)
  let ctx, b = lower_choices loc ctx init_block ntd.non_term_rules
                 loc_fn lower_fn in
  (* Construct the nt_entry. *)
  let m = Anf_common.modul_of_mname mname in
  let nte =
    {nt_name      = ntd.non_term_name;
     nt_inh_attrs;
     nt_typ       = typ;
     nt_code      = seal_block b;
     nt_retvar    = rv;
     nt_loc       = ntd.non_term_loc} in
  (* Add it to the completed non-terminal definitions. *)
  let toc = ValueMap.add (m, nt_name) nte ctx.ctx_toc in
  {ctx with ctx_toc       = toc;
            ctx_free_vars = fvs}

(* A wrapper to intercept the special case of a non-terminal without
   attributes, no temporaries and regexp-convertible rules. *)
let lower_ntd (trace: bool) (ctx: context)
      (tvenv: TypeInfer.VEnv.t) (ntd: TypedAst.non_term_defn)
    : context * TypeInfer.VEnv.t =
  let mname = Ast.(Modul (Mod_inferred ntd.non_term_mod)) in
  (* detect special case *)
  let no_synth_attrs =
    match ntd.non_term_syn_attrs with
      | ALT_decls [] -> true
      | _            -> false in
  let no_inh_attrs = List.length ntd.non_term_inh_attrs = 0 in
  let only_regexp_rules =
    List.for_all
      (TypedAstUtils.is_regexp_rule ctx.ctx_tenv mname)
      ntd.non_term_rules in

  (* Generate local variable names for use in binding and assignment.
     The idea is to transform definitions of the type
         A := <regexp>
     into
         A a' := a=<regexp> { a' := a }
     This is needed to ensure that there is a variable that binds the
     matched value.  Two variables are needed since `a` above is a
     lexically scoped variable that is not visible outside the rule,
     while `a'` is visible outside the rule.
   *)
  let mk_ntd_var i tvenv =
    let ntn = Location.value ntd.non_term_name in
    let ntl = Location.loc ntd.non_term_name in
    (* since `ntn` is uppercase, we can use its lowercase form as a
       non-conflicting local variable name *)
    let nv = String.lowercase_ascii ntn ^ Int.to_string i in
    let nv = Location.mk_loc_val (nv, ()) ntl in
    (* generate a variable for this name *)
    TypeInfer.VEnv.add tvenv nv in
  (* construct the rule element for `{ a' := a }` *)
  let mk_assign_rule_elem nv' nv r_mod r_loc r_aux =
    let act = Ast.({action_stmts =
                      [ {stmt = S_assign ({expr     = E_var nv';
                                           expr_loc = r_loc;
                                           expr_aux = r_aux},
                                          {expr     = E_var nv;
                                           expr_loc = r_loc;
                                           expr_aux = r_aux});
                         stmt_loc = r_loc} ], None;
                    action_loc = r_loc}) in
    Ast.({rule_elem     = RE_action act;
          rule_elem_aux = get_std_typ ctx "unit";
          rule_elem_mod = r_mod;
          rule_elem_loc = r_loc}) in

  let ctx, tvenv, ntd =
    (* update re context if needed *)
    if no_synth_attrs && no_inh_attrs && only_regexp_rules
    then
      (* construct a regexp from the rules *)
      let rx = TypedAstUtils.rules_to_regexp
                 ntd.non_term_mod ntd.non_term_rules in
      let re = Dfa.Dfa_of_regexp.build_re ctx.ctx_re_env rx in
      (* add this to the re environment *)
      let renv = Dfa.Automaton.StringMap.add
                   (Location.value ntd.non_term_name)
                   (rx.regexp_loc, re)
                   ctx.ctx_re_env in
      let r_loc = rx.regexp_loc in
      let r_aux = rx.regexp_aux in
      let r_mod = rx.regexp_mod in
      (* create a simplified rule for the definition *)
      let rle = Ast.({rule_elem      = RE_regexp rx;
                      rule_elem_aux  = r_aux;
                      rule_elem_mod  = r_mod;
                      rule_elem_loc  = r_loc}) in
      (* The non-terminal could not have been named, otherwise the
         initialization analysis should have ensured an action was
         used to set its value, and that action would have made this
         non-terminal not equivalent to a non-regexp. *)
      assert (ntd.non_term_varname = None);
      let nv, tvenv = mk_ntd_var 0 tvenv in
      (* make sure this variable is bound in the rule *)
      let rle = Ast.({rule_elem     = RE_named (nv, rle);
                      rule_elem_aux = r_aux;
                      rule_elem_mod = r_mod;
                      rule_elem_loc = r_loc}) in
      (* use an action to make the bound value visible *)
      let nv', tvenv = mk_ntd_var 1 tvenv in
      let rla = mk_assign_rule_elem nv' nv r_mod r_loc r_aux in
      let rl  = Ast.({rule_rhs   = [rle; rla];
                      rule_temps = [];
                      rule_loc   = rx.regexp_loc}) in
      let ntd = {ntd with non_term_varname = Some nv';
                          non_term_rules   = [rl]} in
      {ctx with ctx_re_env = renv}, tvenv, ntd
    else if ntd.non_term_varname = None
    (* handle common cases of unnamed non-terminals *)
    then
      (* abbreviations *)
      (if List.length ntd.non_term_rules = 1
          && List.length (List.hd ntd.non_term_rules).rule_rhs = 1
       then
         let nv, tvenv = mk_ntd_var 0 tvenv in
         let rl  = List.hd ntd.non_term_rules in
         let rle = List.hd rl.rule_rhs in
         let rle = Ast.({rle with rule_elem = RE_named (nv, rle)}) in
         let nv', tvenv = mk_ntd_var 1 tvenv in
         let r_loc, r_aux = rle.rule_elem_loc, rle.rule_elem_aux in
         let r_mod = rle.rule_elem_mod in
         let rla = mk_assign_rule_elem nv' nv r_mod r_loc r_aux in
         let rl  = Ast.({rl with rule_rhs = [rle; rla]}) in
         let ntd = {ntd with non_term_varname = Some nv';
                             non_term_rules   = [rl]} in
         ctx, tvenv, ntd
       else
         let loc = Location.loc ntd.non_term_name in
         let err = Nonterm_variable_required ntd.non_term_name in
         raise (Error (loc, err))
      )
    else
      ctx, tvenv, ntd in
  (* now dispatch to general case *)
  let ctx = lower_general_ntd trace ctx ntd in
  ctx, tvenv
