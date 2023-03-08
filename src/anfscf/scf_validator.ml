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
open Scf
open Scf_zipper

(* We need to validate the SCF IR in time linear in the instruction
   length.  See discussion of the invariants that need to be validated
   in doc/notes/cfir.txt.  That discussion needs to be moved into this
   file once the ideas stabilize.
 *)

type bitmode =
  | BM_on
  | BM_off

let str_of_bitmode = function
  | BM_on  -> "active"
  | BM_off -> "inactive"

(* We should use a better descriptor for the provenance of a view. *)
type view_entry = Location.t

(* Exit points. *)

type fail_type =
  | FT_fail
  | FT_bitmode
  | FT_choice

let str_of_fail = function
  | FT_fail    -> "fail"
  | FT_bitmode -> "fail-bitmode"
  | FT_choice  -> "fail-choice"

type block_type =
  | BT_then
  | BT_else
  | BT_loop
  | BT_do
  | BT_handler
  | BT_choice_clause
  | BT_choices

let str_of_block_type = function
  | BT_then          -> "then"
  | BT_else          -> "else"
  | BT_loop          -> "loop"
  | BT_do            -> "do"
  | BT_handler       -> "handler"
  | BT_choice_clause -> "choice"
  | BT_choices       -> "start-choices"

type exit_type =
  (* explicit *)
  | EP_explicit_fail of fail_type
  | EP_break
  | EP_continue_choice
  | EP_finish_choice
  | EP_if
  (* implicit *)
  | EP_last_in_block of block_type
  | EP_implicit_fail

let str_of_exit_type = function
  | EP_explicit_fail ft -> (str_of_fail ft)
  | EP_break            -> "break"
  | EP_continue_choice  -> "continue-choice"
  | EP_finish_choice    -> "finish-choice"
  | EP_if               -> "if"
  | EP_last_in_block bt -> "end of " ^ (str_of_block_type bt)
  | EP_implicit_fail    -> "implicit-fail"

type join_state =
  {js_bitmode: bitmode;
   js_views:   view_entry list}

type join_entry = exit_type * bivalent_instr * join_state

type join_type =
  | JP_post_if
  | JP_post_loop
  | JP_post_do
  | JP_post_choices
  | JP_loop_top
  | JP_handler_top
  | JP_choice_top

type join_instr =
  | JI_block of bivalent_instr
  | JI_handler of linear_instr

let id_of_join_instr = function
  | JI_block bi   -> bi.bi_id
  | JI_handler li -> li.li_id

module JoinMap = Map.Make (struct type t = instr_id
                                  let compare = compare
                           end)
module JoinEntries = Set.Make (struct type t = join_entry
                                      let compare = compare
                               end)
(* Validation errors. *)

type view_exit =
  | VE_drop
  | VE_pop

let str_of_view_exit = function
  | VE_drop -> "drop"
  | VE_pop  -> "pop"

type error =
  | V_no_choices
  | V_empty_handler

  (* control flow checks *)
  | V_no_break_target
  | V_no_continue_choice_target
  | V_no_break_in_loop
  | V_no_exit_from_start_choices

  (* end-of-block checks *)
  | V_not_at_block_end of bivalent_instr
  | V_invalid_continuation of exec_next

  (* end-of-definition checks *)
  | V_def_ends_in_bitmode
  | V_def_ends_with_views of int

  (* path consistency errors *)

  (* bitmode inconsistency *)
  | V_bitmode of (* expected *) bitmode * (* actual *) bitmode
  (* view stack underflow *)
  | V_unsafe_exit of view_exit
  (* unbalanced join point *)
  | V_mismatched_views of view_entry list * view_entry list

exception Error of Location.t * error

let error_msg = function
  | V_no_choices ->
      "no choices"
  | V_empty_handler ->
      "empty handler"
  | V_no_break_target ->
      "no target found for break"
  | V_no_continue_choice_target ->
      "no target found for continue-choice"
  | V_no_break_in_loop ->
      "loop does not contain a break"
  | V_no_exit_from_start_choices ->
      "no exit found from start-choices"
  | V_not_at_block_end bi ->
      Printf.sprintf "instruction is not at block end: %s"
        (Scf_printer.str_of_binst bi)
  | V_invalid_continuation en ->
      "a " ^ str_of_next en ^ " continuation is invalid"
  | V_def_ends_in_bitmode ->
      "definition finishes with active bitmode"
  | V_def_ends_with_views nvs ->
      Printf.sprintf "definition finishes with %d active views"
        nvs
  | V_bitmode (exp, act) ->
      Printf.sprintf "expected bitmode is %s, found %s"
        (str_of_bitmode exp) (str_of_bitmode act)
  | V_unsafe_exit ex ->
      Printf.sprintf "%s of view is unsafe" (str_of_view_exit ex)
  | V_mismatched_views (vs, vs') ->
      Printf.sprintf "found paths with %d and %d active views"
        (List.length vs) (List.length vs')

type context =
  {ctx_bitmode:       bitmode;
   ctx_views:         view_entry list;
   ctx_break:         bool;
   ctx_finish_choice: bool;
   ctx_fail_choice:   bool;
   ctx_joins:         JoinEntries.t JoinMap.t}

let merge_flags ctx ctx' =
  {ctx with
    ctx_break         = ctx.ctx_break || ctx'.ctx_break;
    ctx_finish_choice = ctx.ctx_finish_choice
                        || ctx'.ctx_finish_choice;
    ctx_fail_choice   = ctx.ctx_fail_choice
                        || ctx'.ctx_fail_choice}

let join_state_of_context (ctx: context) =
  {js_bitmode = ctx.ctx_bitmode;
   js_views   = ctx.ctx_views}

let add_join ctx (j: join_entry) (tgt: join_instr) : context =
  let join_id = id_of_join_instr tgt in
  let s = match JoinMap.find_opt join_id ctx.ctx_joins with
      | Some s -> JoinEntries.add j s
      | None   -> JoinEntries.singleton j in
  let m = JoinMap.add join_id s ctx.ctx_joins in
  {ctx with ctx_joins = m}

(* Checkers. *)

let in_bitmode (ctx: context) (l: Location.t) : unit =
  match ctx.ctx_bitmode with
    | BM_on  -> ()
    | BM_off -> let err = V_bitmode (BM_on, BM_off) in
                raise (Error (l, err))

let outside_bitmode (ctx: context) (l: Location.t) : unit =
  match ctx.ctx_bitmode with
    | BM_on  -> let err = V_bitmode (BM_off, BM_on) in
                raise (Error (l, err))
    | BM_off -> ()

let match_bitmode_at_join (t: bitmode) (e: bitmode)
      (l: Location.t) =
  if   t <> e
  then let err = V_bitmode (t, e) in
       raise (Error (l, err))

let safe_view_exit (ctx: context) (x: view_exit) (l: Location.t)
    : context =
  match ctx.ctx_views with
    | _::t -> {ctx with ctx_views = t}
    | []   -> let err = V_unsafe_exit x in
              raise (Error (l, err))

let match_views_at_join (t: view_entry list) (e: view_entry list)
      (l: Location.t)
    : unit =
  if   t <> e
  then let err = V_mismatched_views (t, e) in
       raise (Error (l, err))

let check_consistency (p: join_state) (q: join_state) (l: Location.t)
    : unit =
  match_views_at_join p.js_views q.js_views l;
  match_bitmode_at_join p.js_bitmode q.js_bitmode l

(* Validation routines. *)

(* The `z` zipper location is pointing at the instruction `i`. *)
let validate_linear (ctx: context) (i: linear_instr) (z: zctx)
    : context =
  let loc = i.li_loc in
  match i.li with
    | L_enter_bitmode ->
        outside_bitmode ctx loc;
        {ctx with ctx_bitmode = BM_on}
    | L_exit_bitmode ->
        in_bitmode ctx loc;
        {ctx with ctx_bitmode = BM_off}
    | L_fail_bitmode ->
        in_bitmode ctx loc;
        {ctx with ctx_bitmode = BM_off}
    | L_push_view ->
        let ctx_views = loc :: ctx.ctx_views in
        {ctx with ctx_views}
    | L_pop_view ->
        safe_view_exit ctx VE_pop loc
    | L_drop_view ->
        safe_view_exit ctx VE_drop loc
    | L_finish_choice ->
        (* There should be no subsequent instruction in this block. *)
        (if   not (last_in_block z)
         then let bi  = mk_l2b i.li i.li_typ i.li_loc i.li_id in
              let err = V_not_at_block_end bi in
              raise (Error (loc, err)));
        (* Validate control flow target. *)
        (match finish_choice_next loc z with
           | EN_done, _ ->
               {ctx with ctx_finish_choice = true}
           | EN_block t, _ ->
               (* Note the `finish_choice`. *)
               let ctx = {ctx with ctx_finish_choice = true} in
               (* Update join info. *)
               let js  = join_state_of_context ctx in
               let bi  = mk_l2b i.li i.li_typ i.li_loc i.li_id in
               let j   = EP_finish_choice, bi, js in
               let tgt = JI_block t in
               add_join ctx j tgt
           | en, _ ->
               raise (Error (loc, V_invalid_continuation en)))
    | L_continue_choice ->
        let bi = mk_l2b i.li i.li_typ i.li_loc i.li_id in
        (* There should be no subsequent instruction in this block. *)
        (if   not (last_in_block z)
         then let err = V_not_at_block_end bi in
              raise (Error (loc, err)));
        (* Validate control flow target. *)
        (match continue_choice_next loc z with
           | EN_done, _ ->
               raise (Error (loc, V_no_continue_choice_target))
           | EN_block t, _ ->
               (* Update join info. *)
               let js  = join_state_of_context ctx in
               let j   = EP_continue_choice, bi, js in
               let tgt = JI_block t in
               add_join ctx j tgt
           | en, _ ->
               raise (Error (loc, V_invalid_continuation en)))
    | L_fail_choice ->
        let bi = mk_l2b i.li i.li_typ i.li_loc i.li_id in
        (* There should be no subsequent instruction in this block. *)
        (if   not (last_in_block z)
         then let err = V_not_at_block_end bi in
              raise (Error (loc, err)));
        (* Validate control flow target. *)
        (match fail_choice_next loc z with
           | EN_done, _ ->
               {ctx with ctx_finish_choice = true}
           | EN_handler t, _ ->
               (* Note the `fail_choice`. *)
               let ctx = {ctx with ctx_fail_choice = true} in
               (* Update join info. *)
               let js  = join_state_of_context ctx in
               let j   = EP_explicit_fail FT_choice, bi, js in
               let tgt = JI_handler t in
               add_join ctx j tgt
           | EN_block t, _ ->
               (* Note the `fail_choice`. *)
               let ctx = {ctx with ctx_fail_choice = true} in
               (* Update join info. *)
               let js  = join_state_of_context ctx in
               let j   = EP_explicit_fail FT_choice, bi, js in
               let tgt = JI_block t in
               add_join ctx j tgt)
    | _ ->
        (* TODO: variable analysis for other linear instructions. *)
        ctx

(* Validate a block in a given context. *)

(* The `z` zipper location is pointing at the instruction `i`. *)
let rec validate_bivalent (ctx: context) ((i, z): scf_zipper)
        : context =
  let loc = i.bi_loc in
  match i.bi with
    (* Linear instructions. *)

    | B_linear li ->
        validate_linear ctx li z

    (* Bivalent control flow *)

    | B_fail ->
        (* There should be no subsequent instruction in this block. *)
        (if   not (last_in_block z)
         then let err = V_not_at_block_end i in
              raise (Error (loc, err)));
        (match fail_next z with
           | EN_done, _ ->
               ctx
           | EN_handler t, _ ->
               (* Update join info. *)
               let js  = join_state_of_context ctx in
               let j   = EP_explicit_fail FT_fail, i, js in
               let tgt = JI_handler t in
               add_join ctx j tgt
           | EN_block t, _ ->
               (* Update join info. *)
               let js  = join_state_of_context ctx in
               let j   = EP_explicit_fail FT_fail, i, js in
               let tgt = JI_block t in
               add_join ctx j tgt)

    | B_break ->
        (* There should be no subsequent instruction in this block. *)
        (if   not (last_in_block z)
         then let err = V_not_at_block_end i in
              raise (Error (loc, err)));
        (match break_next loc z with
           | EN_done, _ ->
               raise (Error (loc, V_no_break_target))
           | EN_block t, _ ->
               (* Note the presence of a break. *)
               let ctx = {ctx with ctx_break = true} in
               (* Update join info. *)
               let js  = join_state_of_context ctx in
               let j   = EP_break, i, js in
               let tgt = JI_block t in
               add_join ctx j tgt
           | en, _ ->
               raise (Error (loc, V_invalid_continuation en)))

    (* Structured control flow *)

    | B_control {ci = C_if (v, tb, eb); ci_loc = cloc; ci_id = cid} ->
        (* Step past the current instruction, which should always
           succeed. *)
        let z = match step z with
            | None   -> assert false
            | Some z -> z in
        (* Get the context after the `then` block. *)
        let ctxt = match unseal_block tb with
            | [] -> ctx
            | b  -> let zt = Z_ift (v, ([], b), eb, cloc, cid, z) in
                    validate_block ctx b zt in
        (* Get the context after the `else` block. *)
        let ctxe = match unseal_block eb with
            | [] -> ctx
            | b  -> let ze = Z_ife (v, tb, ([], b), cloc, cid, z) in
                    let ctx = {ctx with ctx_joins  = ctxt.ctx_joins} in
                    validate_block ctx b ze in
        (* Check path consistency. *)
        check_consistency (join_state_of_context ctxt)
          (join_state_of_context ctxe) cloc;
        (* A break and other exits could occur in either branch. *)
        let ctx = merge_flags ctxe ctxt in
        (match exec_next z with
           | EN_done, _ ->
               ctx
           | EN_block t, _ ->
               (* Update join info.  Since we've checked path
                  consistency above, we can add a single join point
                  from the if, instead of one each from the end of the
                  `then` and `else` blocks.  TODO: check that this is
                  sound for later processing. *)
               let js  = join_state_of_context ctx in
               let j   = EP_if, i, js in
               let tgt = JI_block t in
               add_join ctx j tgt
           | en, _ ->
               raise (Error (loc, V_invalid_continuation en)))

    | B_control {ci = C_do (b, (h, eh)); ci_loc = cloc; ci_id = cid} ->
        (* Step past the current instruction, which should always
           succeed. *)
        let z = match step z with
            | None   -> assert false
            | Some z -> z in
        (* Process the `do` block. *)
        let ji, ctx = match unseal_block b with
            | [] -> i, ctx
            | b  -> let z = Z_do (([], b), (h, eh), cloc, cid, z) in
                    List.hd (List.rev b), validate_block ctx b z in
        (* Create the join point for the `do` block. *)
        let ctx = match exec_next z with
            | EN_done, _ ->
                ctx
            | EN_block t, _ ->
                let js  = join_state_of_context ctx in
                let j   = EP_last_in_block BT_do, ji, js in
                let tgt = JI_block t in
                add_join ctx j tgt
            | en, _ ->
                raise (Error (loc, V_invalid_continuation en)) in

        (* The starting context for the handler could be the one
           active at the time of any of the failing instructions in
           the do block.  The path invariant says that all these
           contexts are equivalent; so any of them could be used to
           process the handler.

           Since we've just processed all the instructions in the `do`
           block, all failing instructions have registered their join
           states at the handler.  No more will be registered, since
           the handler is not in the scope of any other instructions.

           Special case: what if there are only linear instructions in
           the do block?  Linear instructions don't fail, and so
           cannot join at the handler. If there is no join point, then
           there is no failure, the handler doesn't get executed, and
           hence does not generate a join point of its own, and hence
           does not need to be processed (though it should be logged
           for analysis and potential optimization.)

           Note that H_success handlers create join points at the
           exec_next instruction; this implies these handlers should
           be processed before join points at bivalent instructions
           are validated.
         *)
        (match unseal_handler eh with
           | [] when h = H_failure ->
               let err = V_empty_handler in
               raise (Error (cloc, err))
           | [] ->
               ctx
           | (hh :: _) as eh ->
               (* Lookup a join context for the handler, indexed by
                  the id of its first instruction. *)
               (match JoinMap.find_opt hh.li_id ctx.ctx_joins with
                  | None ->
                      (* No joins!  The handler is (potentially) dead
                         code, and may be optimized away.  *)
                      ctx
                  | Some joins ->
                      assert (not (JoinEntries.is_empty joins));
                      let _, _, {js_bitmode = bm;
                                 js_views   = vs}
                        = JoinEntries.choose joins in
                      (* Initialize an appropriate context and zipper
                         location for the handler. *)
                      let ctxh =
                        let ctx = {ctx with ctx_bitmode = bm;
                                            ctx_views   = vs} in
                        (* We need the original `z`, so hide this
                           under a let. *)
                        let z = Z_doh (b, h, ([], eh), cloc, cid, z) in
                        (* Process the handler. *)
                        validate_handler ctx eh z in
                      let ctx = {ctxh with ctx_bitmode = ctx.ctx_bitmode;
                                           ctx_views   = ctx.ctx_views} in
                      (* Create the join point for the handler.
                         H_success joins at exec_next;
                         H_failure joins at fail_next. *)
                      let ji = List.hd (List.rev eh) in
                      let ji = mk_l2b ji.li ji.li_typ ji.li_loc ji.li_id in
                      match h with
                        | H_success ->
                            (match exec_next z with
                               | EN_done, _ ->
                                   ctx
                               | EN_block t, _ ->
                                   let js  = join_state_of_context ctxh in
                                   let j   = EP_last_in_block BT_handler,
                                             ji, js in
                                   let tgt = JI_block t in
                                   add_join ctx j tgt
                               | en, _ ->
                                   raise (Error (loc, V_invalid_continuation en)))
                        | H_failure ->
                            (match fail_next z with
                               | EN_done, _ ->
                                   ctx
                               | EN_handler t, _ ->
                                   let js  = join_state_of_context ctxh in
                                   let j   = EP_last_in_block BT_handler,
                                             ji, js in
                                   let tgt = JI_handler t in
                                   add_join ctx j tgt
                               | EN_block t, _ ->
                                   let js  = join_state_of_context ctxh in
                                   let j   = EP_last_in_block BT_handler,
                                             ji, js in
                                   let tgt = JI_block t in
                                   add_join ctx j tgt)))

    | B_control {ci = C_loop (infinite, b); ci_loc = cloc; ci_id = cid} ->
        (* Step past the current instruction, which should always
           succeed. *)
        let z = match step z with
            | None   -> assert false
            | Some z -> z in
        (* Check for associated break in loop. *)
        let outer_break = ctx.ctx_break in
        let ctxl = match unseal_block b with
            | [] -> ctx
            | b  -> let z = Z_loop (infinite, ([], b), cloc, cid, z) in
                    let ctx = {ctx with ctx_break = false} in
                    let ctx = validate_block ctx b z in
                    if   infinite || ctx.ctx_break
                    then ctx
                    else let err = V_no_break_in_loop in
                         raise (Error (cloc, err)) in
        (* Note that the loop block is special; it joins to the top of
           the block, and not the exec_next instruction.  What context
           should we use for the exec_next instruction?  Ideally, it
           should be the context of the associated break(s).  However,
           the analysis is simplified if we impose a stronger
           invariant: the state on loop exit should be the same as the
           state on loop entry.  With this, we can use the entry state
           as the context for exec_next.
         *)
        check_consistency (join_state_of_context ctx)
          (join_state_of_context ctxl) cloc;
        let ctx = merge_flags ctx ctxl in
        {ctx with ctx_break = outer_break}

    | B_control {ci = C_start_choices (fid, muts, b); ci_loc = cloc;
                 ci_id = cid} ->
        (* Step past the current instruction, which should always
           succeed. *)
        let z = match step z with
            | None   -> assert false
            | Some z -> z in
        (* Check for associated exits. *)
        let outer_finish = ctx.ctx_finish_choice in
        let outer_fail   = ctx.ctx_fail_choice in
        let ctx = match unseal_block b with
            | [] ->
                raise (Error (cloc, V_no_choices))
            | b  ->
                let z = Z_start_choices (fid, muts, ([], b), cloc, cid, z) in
                let ctx = validate_block ctx b z in
                if   not (ctx.ctx_finish_choice || ctx.ctx_fail_choice)
                then let err = V_no_exit_from_start_choices in
                     raise (Error (cloc, err))
                else ctx in
        (* This instruction doesn't itself join another instruction;
           rather, the instructions in the embedded block have various
           join points.  This is enforced by the above invariant that
           the only exits from a `start-choices` block are via
           `finish-choice` and `fail-choice`.

           The above check ensures that `finish-choice` or
           `fail-choice` are among the exits, but not that they are
           the *only* exits.  That check is done by
           `finish_choice_next`, `fail_choice_next` and `fail_next`
           functions in `scf_zipper`.
         *)
        {ctx with ctx_finish_choice = outer_finish;
                  ctx_fail_choice   = outer_fail}

    (* Other bivalent instructions. *)

    | B_bits _
    | B_align _
    | B_pad _
    | B_collect_checked_bits _
    | B_check_bits _
    | B_constraint _
    | B_exec_dfa _
    | B_scan _
    | B_call_nonterm _
    | B_require_remaining _ ->
        (* Check for valid target for implicit failure. *)
        (match fail_next z with
           | EN_done, _ ->
               ctx
           | EN_handler t, _ ->
               (* Update join info. *)
               let js  = join_state_of_context ctx in
               let j   = EP_implicit_fail, i, js in
               let tgt = JI_handler t in
               add_join ctx j tgt
           | EN_block t, _ ->
               (* Update join info. *)
               let js  = join_state_of_context ctx in
               let j   = EP_implicit_fail, i, js in
               let tgt = JI_block t in
               add_join ctx j tgt)

and validate_block ctx (b: block) (z: zctx) : context =
  (* Note that instructions in the non-empty block `b` are in
     execution order; and `z` points to the first instruction in the
     block. *)
  let rec validate ctx z = function
    | i :: t -> let ctx = validate_bivalent ctx (i, z) in
                (match step z with
                   | Some z -> validate ctx z t
                   | None   -> assert (t = []);
                               ctx)
    | []     -> ctx in
  validate ctx z b

and validate_handler ctx (h: handler) (z: zctx) : context =
  (* Note that instructions in the non-empty handler `h` are in
     execution order; and `z` points to the first instruction in the
     handler. *)
  let rec validate ctx z = function
    | i :: t -> let ctx = validate_linear ctx i z in
                (match step z with
                   | Some z -> validate ctx z t
                   | None   -> assert (t = []);
                               ctx)
    | []     -> ctx in
  validate ctx z h

(* Validate a definition block. *)

let check_def_block _nt (b: sealed_block) (l: Location.t) =
  let init_ctx = {ctx_bitmode       = BM_off;
                  ctx_views         = [];
                  ctx_break         = false;
                  ctx_finish_choice = false;
                  ctx_fail_choice   = false;
                  ctx_joins         = JoinMap.empty} in
  let b   = unseal_block b in
  let z   = Z_block ([], b) in
  let ctx = validate_block init_ctx b z in
  (* Invariants:
     a: The context at the end should have no net effect on the runtime
        view and bit state.
     b: At each join point, the view and bit state along each joining
        path should be the same (i.e. "consistent").
   *)

  (* a: *)
  (if   ctx.ctx_bitmode = BM_on
   then let err = V_def_ends_in_bitmode in
        raise (Error (l, err)));
  (if   ctx.ctx_views <> []
   then let err = V_def_ends_with_views (List.length ctx.ctx_views) in
        raise (Error (l, err)));

  (* b: *)
  JoinMap.iter (fun _i jset ->
      let jls = List.of_seq (JoinEntries.to_seq jset) in
      match jls with
        | [] ->
            (* We never create an empty entry. *)
            assert false
        | ex :: t ->
            (* Treat the first join as exemplar, and check that all other
               joins are equivalent. *)
            let _, _, ejs = ex in
            List.iter (fun j ->
                let _, {bi_loc = l;_}, js = j in
                check_consistency ejs js l
              ) t
    ) ctx.ctx_joins

(* Validate the whole spec. *)

let validate (spec: spec_scf) (_debug: bool) : unit =
  (* Validate statics. *)
  let nt = Anf.M_name "_global", "_statics" in
  check_def_block nt spec.scf_statics (Location.ghost_loc);

  (* Validate each non-terminal. *)
  ValueMap.iter (fun nt ent ->
      check_def_block nt ent.nt_code ent.nt_loc
    ) spec.scf_globals
