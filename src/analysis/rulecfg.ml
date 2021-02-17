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

(* A control-flow graph for production rules in the typed AST *)

module Location = Parsing.Location
module TE = Typing.TypingEnvironment

open Parsing.Ast
open Typing.TypeInfer

type typ = Typing.MultiEquation.crterm

(* TODO: move this into an astutils module *)

(* We track bindings that are of two types:
 *
 * . atomic symbols that are used for inherited attributes, pattern
 *   bindings in let/case expressions, and in named rule-elements
 * . record fields, such as those used for synthesized attributes
 *
 * Although the AST permits more general cases of the latter type
 * (e.g. [(e).f], where [e] is an expression and [f] is a record
 * field), we only track the case where [e] is an atomic symbol. This
 * may need to change when grammar modules are implemented, where we
 * may need to handle [M.e.f], where [e] is atomic and [M] is a module
 * name.
 *)

module Bindings = struct
  module B = Set.Make(struct
                 type t = varid * string option
                 let compare = compare
               end)
  include B

  let singleton d = add d empty
end

let vars_of_pattern (p: (typ, varid) pattern) : Bindings.t =
  let rec add set p =
    match p.pattern with
      | P_wildcard | P_literal _ ->
          set
      | P_var v ->
          Bindings.add (snd (Location.value v), None) set
      | P_variant (_, ps) ->
          List.fold_left add set ps in
  add Bindings.empty p

(* if a [bound] variable set is provided, this computes the free
 * variables (i.e. that are not in [bound]) of the expression.
 *)
let free_vars_of_expr (e: (typ, varid) expr) (bound: Bindings.t option)
    : Bindings.t =
  let rec add ((set, bound) as acc) e =
    match e.expr with
      | E_var v ->
          let id = snd (Location.value v), None in
          if   Bindings.mem id bound
          then acc
          else Bindings.add id set, bound
      | E_constr (_, es) ->
          List.fold_left add acc es
      | E_record fs ->
          List.fold_left (fun acc (_, e) -> add acc e) acc fs
      | E_apply (f, args) ->
          List.fold_left add (add acc f) args
      | E_case (e, cls) ->
          List.fold_left (fun (set, bound) (p, e) ->
              let bound = Bindings.union bound (vars_of_pattern p) in
              add (set, bound) e
            ) (add acc e) cls
      | E_let (p, e', e) ->
          let (set', bound') = add acc e' in
          let bound' = Bindings.union bound' (vars_of_pattern p) in
          add (set', bound') e
      | E_binop (_, l, r) ->
          add (add acc l) r
      | E_literal _ | E_mod_member _ ->
          acc
      | E_field ({expr = E_var v; _}, f) ->
          let id = snd (Location.value v), Some (Location.value f) in
          if   Bindings.mem id bound
          then acc
          else Bindings.add id set, bound
      | E_field (e, _) | E_unop (_, e) | E_match (e, _) | E_cast (e, _) ->
          add acc e in
  let bound = match bound with
      | None   -> Bindings.empty
      | Some b -> b in
  fst (add (Bindings.empty, bound) e)

let pattern_of_var v loc aux : (typ, varid) pattern =
  {pattern = P_var v;
   pattern_loc = loc;
   pattern_aux = aux}

(* a node for the basic elements of the grammar language *)
type gn =
  | GN_regexp
  | GN_type of ident
  | GN_constraint of (typ, varid) expr
  | GN_non_term of ident (* stripped of inherited attributes *)

type ('v) gnode =
  {gnode: gn;
   gnode_aux: 'v}

(* a node for basic non-branching expressions (including grammar
 * constraints) and the assignment statement.
 *)
type en =
  | EN_expr of (typ, varid) expr
  | EN_defn of (typ, varid) pattern
  (* variable/record-field assignment *)
  | EN_binding_assign of Bindings.elt * (typ, varid) expr
  (* other assignments *)
  | EN_assign of (typ, varid) expr * (typ, varid) expr

type ('v) enode =
  {enode: en;
   enode_aux: 'v}

(* dataflow node *)
module Node = struct
  type ('e, 'x, 'v) node =
    | N_enode: 'v enode         -> (Block.o, Block.o, 'v) node
    | N_gnode: 'v gnode         -> (Block.o, Block.o, 'v) node
    | N_label: Label.label      -> (Block.c, Block.o, 'v) node
    | N_jumps: Label.label list -> (Block.o, Block.c, 'v) node

  let entry_label (type x v) (n: (Block.c, x, v) node) =
    match n with
      | N_label l -> l
      (* this should not be needed *)
      | _ -> assert false

  let successors (type e v) (n: (e, Block.c, v) node) =
    match n with
      | N_jumps l -> l
      (* this should not be needed *)
      | _ -> assert false
end

(* the blocks of the CFG *)

module G = Graph.MkGraph(Node)
module B = G.Block
module D = G.Body

(* Each node stores the bindings used and defined by it *)
type v =
  {node_use: Bindings.t;
   node_def: Bindings.t}

type opened = (Block.c, Block.o, v) B.block
type closed = (Block.c, Block.c, v) B.block

let add_expr (env: Bindings.t) (b: opened) (e: (typ, varid) expr) =
  let u = free_vars_of_expr e (Some env) in
  let v = {node_use = u; node_def = Bindings.empty} in
  let n = {enode = EN_expr e; enode_aux = v} in
  B.snoc b (N_enode n)

let add_pattern (_: Bindings.t) (b: opened) (p: (typ, varid) pattern) =
  (* pattern matching binds and initializes its variables *)
  let d = vars_of_pattern p in
  let v = {node_use = Bindings.empty; node_def = d} in
  let n = {enode = EN_defn p; enode_aux = v} in
  B.snoc b (N_enode n)

let add_binding_assign (env: Bindings.t) (b: opened) l e =
  let u = free_vars_of_expr e (Some env) in
  let d = Bindings.singleton l in
  let v = {node_use = u; node_def = d} in
  let n = {enode = EN_binding_assign (l, e); enode_aux = v} in
  B.snoc b (N_enode n)

let add_assign (env: Bindings.t) (b: opened) l e =
  (* the lhs is a general expr, so use an empty def *)
  let u = free_vars_of_expr e (Some env) in
  let v = {node_use = u; node_def = Bindings.empty} in
  let n = {enode = EN_assign (l, e); enode_aux = v} in
  B.snoc b (N_enode n)

let new_labeled_block (l: Label.label) : opened =
  let h = Node.N_label l in
  B.join_head h B.empty

let new_block () : Label.label * opened =
  let l = Label.fresh_label () in
  l, new_labeled_block l

let end_block (b: opened) (l: Label.label list) : closed =
  let t = Node.N_jumps l in
  B.join_tail b t

(* cfg context for expression language: bound constants, accumulated
 * closed blocks, and current open block *)
type ectx = Bindings.t * closed list * opened

(* Statements are added to the end of an opened block, giving the same
 * or different opened block for the next addition.  Any blocks closed
 * during this addition are added to the closed list.
 *)
let rec add_stmt (ctx: ectx) (s: (typ, varid) stmt) : ectx =
  let bound, closed, b = ctx in
  match s.stmt with
    | S_assign ({expr = E_var v; _}, e) ->
        let l = snd (Location.value v), None in
        let b = add_binding_assign bound b l e in
        bound, closed, b
    | S_assign ({expr = E_field ({expr = E_var v; _}, f); _}, e) ->
        let l = snd (Location.value v), Some (Location.value f) in
        let b = add_binding_assign bound b l e in
        bound, closed, b
    | S_assign (l, e) ->
        let b = add_assign bound b l e in
        bound, closed, b
    | S_let (p, e, stmts) ->
        let b = add_expr bound b e in
        let b = add_pattern bound b p in
        List.fold_left add_stmt (bound, closed, b) stmts
    | S_case (e, cls) ->
        let b = add_expr bound b e in
        (* [b] will be closed below with the labels for the new blocks
         * for the clauses.  Each of those blocks will need to jump
         * to a new continuation block.
         *)
        let cl, cb = new_block () in
        let (lbls, closed) =
          List.fold_left (fun (lbls, closed) (p, ss) ->
              let l, b = new_block () in
              let b = add_pattern bound b p in
              let _, closed, b =
                List.fold_left add_stmt (bound, closed, b) ss in
              let c = end_block b [cl] in
              (l :: lbls), c :: closed
            ) ([], closed) cls in
        let c = end_block b lbls in
        bound, c :: closed, cb

let add_gnode (b: opened) gn =
  let v = {node_use = Bindings.empty; node_def = Bindings.empty} in
  let g = {gnode = gn; gnode_aux = v} in
  B.snoc b (N_gnode g)

(* Regular expressions use similar combinators as the production rules
 * for attributed non-terminals; they are separated out in the AST for
 * convenience in the typing rules, and they will likely also help in
 * code generation.  For control-flow convenience however, we express
 * the regexp combinators in terms of the combinators for the
 * attributed rule elements.  We leave only the primitive regexps:
 * literals and wildcards.
 *)
let rec lift_regexp rx =
  let wrap r =
    {rule_elem     = r;
     rule_elem_loc = rx.regexp_loc;
     rule_elem_aux = rx.regexp_aux} in
  match rx.regexp with
    | RX_literals _ | RX_wildcard ->
        wrap (RE_regexp rx)
    | RX_type id ->
        wrap (RE_non_term (id, None))
    | RX_star (re', oe) ->
        let r' = lift_regexp re' in
        wrap (RE_star (r', oe))
    | RX_opt rx' ->
        wrap (RE_opt (lift_regexp rx'))
    | RX_choice rxs ->
        wrap (RE_choice (List.map lift_regexp rxs))
    | RX_seq rxs ->
        wrap (RE_seq (List.map lift_regexp rxs))

(* Rule elements always generate closed blocks headed by the given
 * label, and parsing failures shift control to the label of the
 * current choice block.  The label for the block for the success
 * continuation is returned, along with the updated list of closed
 * blocks.
 *
 * TODO: is it an invariant that the output failure continuation is
 * always the same as the input one?
 *)
type scont = Next of Label.label (* success continuation *)
type fcont = Fail of Label.label (* failure continuation *)

(* cfg context for a rule *)
type rctx  = Bindings.t * closed list * scont * fcont

let rec add_rule_elem (ctx: rctx) (r: (typ, varid) rule_elem)
        : rctx =
  let env, closed, ((Next next) as sc), ((Fail fail) as fc) = ctx in
  let b = new_labeled_block next in
  let finish b =
    let next = Label.fresh_label () in
    let c = end_block b [next; fail] in
    env, c :: closed, Next next, fc in
  match r.rule_elem with
    | RE_regexp {regexp = RX_literals _; _}
    | RE_regexp {regexp = RX_wildcard; _} ->
        let b = add_gnode b GN_regexp in
        finish b
    | RE_regexp rx ->
        let r' = lift_regexp rx in
        add_rule_elem ctx r'
    | RE_non_term (id, oias) ->
        let b = match oias with
            | None -> b
            | Some ias ->
                List.fold_left (fun b (_, e) ->
                    add_expr env b e
                  ) b ias in
        let b = add_gnode b (GN_type id) in
        finish b
    | RE_constraint e ->
        let b = add_expr env b e in
        finish b
    | RE_action {action_stmts = ss, oe; _}->
        let ectx = env, closed, b in
        let env, closed, b = List.fold_left add_stmt ectx ss in
        let b = match oe with
            | None -> b
            | Some e -> add_expr env b e in
        (* create a new label for the success continuation *)
        let next' = Label.fresh_label () in
        let c = end_block b [next'] in
        env, c :: closed, Next next', fc
    | RE_named (n, r') ->
        (* [n] will only be defined in the success continuation of
         * [r'].
         *)
        let env, closed', Next next', fc' = add_rule_elem ctx r' in
        assert (fc == fc');
        let b = new_labeled_block next' in
        let p = pattern_of_var n r.rule_elem_loc r.rule_elem_aux in
        let b = add_pattern env b p in
        (* We just fall through to the next block.
         * TODO: optimize this out, either by looking up the [next]
         * block in a context of opened blocks at the top of
         * [add_rule_elem], or by a subsequent post-processing
         * pass.
         *)
        let next = Label.fresh_label () in
        let c = end_block b [next] in
        env, c :: closed', Next next, fc
    | RE_seq rs ->
        List.fold_left (fun ctx r -> add_rule_elem ctx r) ctx rs
    | RE_choice rs ->
        (* All the [rs] will share a common success continuation, but
         * the failure continuation will be where the next choice
         * element will be placed.  However, the whole choice needs to
         * fail to the input failure continuation.
         *)
        (* common success continuation *)
        let next' = Label.fresh_label () in
        (* first fail continuation *)
        let fail' = Label.fresh_label () in
        let env, closed, Next f', _ =
          List.fold_left
            (fun ctx r ->
              let env, closed, Next n', Fail f' = add_rule_elem ctx r in
              (* join [n'] to the common success continuation [next'].
               * TODO: optimize this fall-through, similar to the
               * RE_named case.
               *)
              let succ = new_labeled_block n' in
              let c = end_block succ [next'] in
              (* create a failure continuation for the next choice *)
              let fail' = Label.fresh_label () in
              (* the next choice uses the failure continuation for [r] *)
              env, c :: closed, Next f', Fail fail'
            )
            (* the first choice will be placed in [next] and will
             * fail to the newly generated [fail']
             *)
            (env, closed, sc, Fail fail') rs in
        (* the last failure continuation should jump to the original *)
        let f = new_labeled_block f' in
        let c = end_block f [fail] in
        (* continue at the common success continuation and the
         * original failure continuation
         *)
        env, c :: closed, Next next', fc
    | RE_star (r', Some e) ->
        (* The bound [e] is evaluated before [r'] is matched; [r']
         * also loops back to the beginning of its block and so will
         * need its own block.  So [e] goes into its own closed
         * non-failing block that continues with the block for [r'].
         *)
        let b = add_expr env b e in
        let next = Label.fresh_label () in
        let c = end_block b [next] in
        let ctx = env, c :: closed, Next next, fc in
        let r = {r with rule_elem = RE_star (r', None)} in
        (* recurse to the unbounded case *)
        add_rule_elem ctx r
    | RE_star (r', None) ->
        (* The rule elem [r] cannot fail, as it either loops on
         * success of [r'] or fails through to the success
         * continuation.  This is handled as follows:
         * if adding [r'] to [next] generates success continuation
         * label [next'], then in [next'] we put the loop to [next] as
         * well as a continuation to a new block [next'']
         * (corresponding to the failure case of [r']), and we return
         * next'' as the success continuation. [r'] is given a new
         * [fail'] continuation, which just jumps to [next''].
         *   next:r' -> next': jump [next, next'']  (success)
         *           -> fail': jump [next'']        (failure)
         * The original [fail] continuation is retained as the failure
         * continuation of the final context.
         *)
        let fail' = Label.fresh_label () in
        let ctx'  = env, closed, sc, Fail fail' in
        let env, closed, Next next', fc' = add_rule_elem ctx' r' in
        assert (fc' = fc);
        let next''  = Label.fresh_label () in
        let success = new_labeled_block next' in
        let success = end_block success [next; next''] in
        let failure = new_labeled_block fail' in
        let failure = end_block failure [next''] in
        let closed  = failure :: success :: closed in
        (* the new success continuation is [next''], and new failure
         * continuation is the original one provided *)
        env, closed, Next next'', fc
    | RE_opt r' ->
        (* The regexp [r] cannot fail, so [r'] is given a custom fail'
         * continuation, which jumps to its success continuation.
         *)
        let fail' = Label.fresh_label () in
        let ctx'  = env, closed, sc, Fail fail' in
        let env, closed, Next next', fc' = add_rule_elem ctx' r' in
        assert (fc' = Fail fail');
        let fail = new_labeled_block fail' in
        let fail = end_block fail [next'] in
        (* the new success continuation is [next'], and new fail
         * continuation is the original one provided *)
        env, fail :: closed, Next next', fc
    | RE_epsilon ->
        (* this is a nop *)
        ctx
    | RE_at_pos (e, r') | RE_at_buf (e, r') ->
        (* [e] is evaluated before [r'] is matched, so [e] goes into
         * its own closed non-failing block that continues with the
         * block for [r'].
         *)
        let b = add_expr env b e in
        let next = Label.fresh_label () in
        let c = end_block b [next] in
        let ctx = env, c :: closed, Next next, fc in
        add_rule_elem ctx r'
    | RE_map_bufs (e, r') ->
        (* [e] is evaluated once, but [r'] is loops back to itself
         * (once for each element of [e]).  So the structure is
         * similar to that for a bounded repeat, except that this
         * fails if any instance of [r'] fails.
         *)
        let b = add_expr env b e in
        let next = Label.fresh_label () in
        let c = end_block b [next] in
        let closed = c :: closed in
        let ctx = env, closed, Next next, fc in
        let env, closed, Next next', fc' = add_rule_elem ctx r' in
        assert (fc == fc');
        (* add a loop in [next'] back to [r']'s [next] block, and
         * succeed to a new [next''].
         *)
        let next'' = Label.fresh_label () in
        let b = new_labeled_block next' in
        let c = end_block b [next; next''] in
        env, c :: closed, Next next'', fc

(* A CFG for a production rule. *)
let rule_to_cfg
      (tenv: TE.environment)
      (env: Bindings.t)
      (ntd: (typ, varid) non_term_defn)
      (r: (typ, varid) rule) =
  (* lookup type info for the non-terminal *)
  let ntnm = Location.value ntd.non_term_name in
  let nti, nts = match TE.lookup_non_term tenv (NName ntnm) with
      | Some t -> t
      | None   -> assert false in
  (* The cfg needs an entry label and block, which will contain the
   * setup for the rule, viz. the binding for the non-terminal itself
   * (if present), and the attributes bindings and temporaries.
   *)
  let entry_lbl = Label.fresh_label () in
  let b = new_labeled_block entry_lbl in
  (* add non-terminal variable name if present *)
  let b = match ntd.non_term_varname with
      | None ->
          b
      | Some v ->
          (* this will have the type of the non-terminal *)
          let p = pattern_of_var v (Location.loc v) nts in
          add_pattern env b p in
  (* add inherited attributes *)
  let b = List.fold_left (fun b (ia, _) ->
              let ian, _ = Location.value ia in
              let iloc = Location.loc ia in
              (* we could loop over [nti] itself instead of looking up,
               * but this enables an extra asserted consistency check
               *)
              let iat =
                match Typing.Misc.StringMap.find_opt ian (fst nti) with
                  | None -> assert false
                  | Some (t, _) -> t in
              let p = pattern_of_var ia iloc iat in
              add_pattern env b p
            ) b ntd.non_term_inh_attrs in
  (* add rule temporaries *)
  let b = List.fold_left (fun b (tv, _, te) ->
              let loc = Location.loc tv in
              let p = pattern_of_var tv loc te.expr_aux in
              add_pattern env b p
            ) b r.rule_temps in
  (* allocate a label for the block to start the rule itself *)
  let next = Label.fresh_label () in
  (* join the entry/setup block to the rule block *)
  let c = end_block b [next] in
  (* allocate a failure label for the whole rule *)
  let fail = Label.fresh_label () in
  (* the initial context *)
  let ctx = env, [c], Next next, Fail fail in
  (* add the rule elements *)
  let _, closed, _, _ =
    List.fold_left add_rule_elem ctx r.rule_rhs in
  (* construct the graph body *)
  let body = List.fold_left D.add_block D.empty closed in
  (* and the graph itself *)
  G.from_body body
