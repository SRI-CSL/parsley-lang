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

(* An analysis to ensure that all synthesized attributes of a
   non-terminal are assigned in each of its production rules, and no
   uninitialized variables are used in any expression.  *)

module Location = Parsing.Location
open Parsing.Ast
module TE = Typing.TypingEnvironment
open Typing.TypeInfer
open Typing.TypedAstUtils
open Flow
open Dataflow

type typ = Typing.MultiEquation.crterm

(* A binding is represented by its unique identifier and optional
 * field.  Its name and location are tracked for error reporting
 * purposes, but they are not used for comparisons. *)
type binding = varid * string option * (string * Location.t)
let binding_to_string (id, fo, (n, _)) =
  let is = varid_to_string id in
  match fo with
    | Some f -> Printf.sprintf "%s[%s].%s" n is f
    | None   -> Printf.sprintf "%s[%s]" n is

type init_var_error =
  | Use_of_uninit_var of binding * Location.t
  | Unnamed_attributed_nonterminal of ident
  | Unassigned_attribute of ident * string * Location.t

exception Error of init_var_error

let msg m loc =
  Printf.sprintf m (Location.str_of_loc loc)

let error_msg = function
  | Use_of_uninit_var ((_v, optf, (n, _)), loc) ->
      msg "%s:\n %s may be used uninitialized.\n"
        loc
        (match optf with
           | None -> n
           | Some f -> Printf.sprintf "%s.%s" n f)
  | Unnamed_attributed_nonterminal nt ->
      msg
        "%s:\n non-terminal %s with synthetic attributes needs to be  given a local name.\n"
        (Location.loc nt) (Location.value nt)
  | Unassigned_attribute (nt, f, loc) ->
      msg "%s:\n attribute %s of %s may be uninitialized at the end of this rule.\n"
        loc f (Location.value nt)

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

let compare_binding (v, f, _ig) (v', f', _ig') =
  compare (v, f) (v', f')

let equal_binding (v, f, _ig) (v', f', _ig') =
  v = v' && f = f'

module Bindings = struct
  module B = Set.Make(struct
                 type t = binding
                 let compare = compare_binding
               end)
  include B

  let print b =
    let es = List.map binding_to_string (elements b) in
    String.concat ", " es
end

let vars_of_pattern (p: (typ, varid) pattern) : Bindings.t =
  let rec add set p =
    match p.pattern with
      | P_wildcard | P_literal _ ->
          set
      | P_var v ->
          let v  = Location.value v in
          let ig = fst v, p.pattern_loc in
          Bindings.add (snd v, None, ig) set
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
          let v' = Location.value v in
          let ig = fst v', Location.loc v in
          let id = snd v', None, ig in
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
      | E_recop (_, _, e) ->
          add acc e
      | E_bitrange (e, _, _) ->
          add acc e
      | E_literal _ | E_mod_member _ ->
          acc
      | E_field ({expr = E_var v; _}, f) ->
          let v  = Location.value v in
          let ig = fst v, e.expr_loc in
          let id = snd v, Some (Location.value f), ig in
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

let print_gn = function
  | GN_regexp ->
      "(gn: <regexp>)"
  | GN_type t ->
      Printf.sprintf "(gn: <type> %s)" (Location.value t)
  | GN_constraint _ ->
      Printf.sprintf "(gn: <constraint>)"
  | GN_non_term n ->
      Printf.sprintf "(gn: <non-term> %s)" (Location.value n)

type ('v) gnode =
  {gnode: gn;
   gnode_loc: Location.t;
   gnode_aux: 'v}

let print_gnode gn =
  print_gn gn.gnode

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

let print_en = function
  | EN_expr _           -> "(en: <expr>)"
  | EN_defn _           -> "(en: <defn>)"
  | EN_binding_assign _ -> "(en: <binding-assign>)"
  | EN_assign _         -> "(en: <assign>)"

type ('v) enode =
  {enode: en;
   enode_loc: Location.t;
   enode_aux: 'v}

let print_enode en =
  print_en en.enode

(* Dataflow node *)

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

  let print (type e x v) (n: (e, x, v) node) =
    match n with
      | N_gnode gn -> print_gnode gn
      | N_enode en -> print_enode en
      | N_label l  -> Printf.sprintf "(N: label %s)" (Label.to_string l)
      | N_jumps ls -> Printf.sprintf "(N: jumps %s)"
                        (String.concat ", " (List.map Label.to_string ls))

  let loc (type v) (n: (Block.o, Block.o, v) node) =
    match n with
      | N_gnode gn -> gn.gnode_loc
      | N_enode en -> en.enode_loc
      (* this should not be needed *)
      | _ -> assert false
end

(* The CFG *)

module G = Graph.MkGraph (Node)
module B = G.Block
module D = G.Body

(* Reaching definitions are bindings labelled with their assigning
 * block.  A binding without a label has been declared but not
 * defined. *)
module ReachingDefns = struct
  module RD = Set.Make(struct
                  type t = binding * Label.label option
                  let compare ((v, f, _), l) ((v', f', _), l') =
                    compare (v, f, l) (v', f', l')
                end)
  include RD

  (* utility for debugging *)
  let entry_to_string (b, ol) =
      let sl = match ol with
          | None   -> "?"
          | Some l -> Label.to_string l in
      Printf.sprintf "%s@%s" (binding_to_string b) sl

  (* checks whether a binding has been declared (or defined) *)
  let binding_declared ((v, f, _) as _b) rd =
    exists (fun (((v', f', _) as _b', _) as _ent) ->
        match f, f' with
          (* exact match *)
          | Some f, Some f' -> v = v' && f = f'
          | None,   None    -> v = v'
          (* a more general binding is declared *)
          | Some _, None    -> v = v'
          | _               -> false
      ) rd

  (* Add new definitions *)
  let define (bs: Bindings.t) (l: Label.label) (rd: t) : t =
    List.fold_left (fun rd b ->
        (* remove any existing undefined binding *)
        let rd = filter
                   (function
                    | (b', None) when equal_binding b b' -> false
                    | _                                  -> true
                   )
                   rd in
        add (b, Some l) rd
      ) rd (Bindings.elements bs)

  (* A binding is possibly undefined if a possibly more general
   * declared but undefined binding is present *)
  let possibly_undefined ((v, f, _) as b: binding) (rd: t) : bool =
    (* the binding should have been declared *)
    assert (binding_declared b rd);
    exists (fun (((v', f', _), ol) as _ent) ->
        let res =
          match f', f, ol with
            (* existing undefined binding is possibly more general *)
            | None, _, None -> v = v'
            (* existing undefined binding is as specific *)
            | Some f', Some f, None -> v = v' && f = f'
            | _, _, _ -> false in
        (*
        Printf.eprintf "   [possibly_undefined: checking %s against %s: %s]\n"
          (binding_to_string b) (entry_to_string _ent)
          (if res then "T" else "F");
         *)
        res
      ) rd
end

(* The lattice for the reaching definitions analysis *)
module IVLattice = struct
  type t = ReachingDefns.t

  let bottom = ReachingDefns.empty

  let join a b =
    (if   ReachingDefns.equal a b
     then NoChange else SomeChange),
    ReachingDefns.union a b

  let print rd =
    let print (b, ol) =
      Printf.sprintf "%s@%s"
        (binding_to_string b)
        (match ol with
           | Some l -> Label.to_string l
           | None   -> "?") in
    let es = List.map print (ReachingDefns.elements rd) in
    String.concat ", " es
end

(* Each node stores the bindings used and defined by it *)
type v =
  {node_use: Bindings.t;
   node_def: Bindings.t * Label.label}

let print_v v =
  Printf.sprintf "[use: %s] [def: %s]"
    (Bindings.print v.node_use) (Bindings.print (fst v.node_def))

type opened = (Block.c, Block.o, v) B.block
type closed = (Block.c, Block.c, v) B.block

let add_expr (env: Bindings.t) (b: opened) (e: (typ, varid) expr) =
  let l = B.entry_label b in
  let u = free_vars_of_expr e (Some env) in
  let v = {node_use = u; node_def = Bindings.empty, l} in
  let n = {enode = EN_expr e; enode_loc = e.expr_loc; enode_aux = v} in
(*  Printf.eprintf "\t%s adding %s: %s\n"
    (Label.to_string l) (Node.print (N_enode n)) (print_v v);*)
  B.snoc b (N_enode n)

let add_pattern (_: Bindings.t) (b: opened) (p: (typ, varid) pattern) =
  (* pattern matching binds and initializes its variables *)
  let l = B.entry_label b in
  let d = vars_of_pattern p in
  let v = {node_use = Bindings.empty; node_def = d, l} in
  let n = {enode = EN_defn p; enode_loc = p.pattern_loc; enode_aux = v} in
(*  Printf.eprintf "\t%s adding %s: %s\n"
    (Label.to_string l) (Node.print (N_enode n)) (print_v v);*)
  B.snoc b (N_enode n)

let add_binding_assign (env: Bindings.t) (b: opened) a e =
  let l = B.entry_label b in
  let u = free_vars_of_expr e (Some env) in
  let d = Bindings.singleton a in
  let v = {node_use = u; node_def = d, l} in
  let n = {enode = EN_binding_assign (a, e);
           enode_loc = e.expr_loc;
           enode_aux = v} in
(*  Printf.eprintf "\t%s adding %s: %s\n"
    (Label.to_string l) (Node.print (N_enode n)) (print_v v);*)
  B.snoc b (N_enode n)

let add_assign (env: Bindings.t) (b: opened) a e =
  let l = B.entry_label b in
  (* the lhs is a general expr, so use an empty def *)
  let u = free_vars_of_expr e (Some env) in
  let v = {node_use = u; node_def = Bindings.empty, l} in
  let n = {enode = EN_assign (a, e); enode_loc = e.expr_loc; enode_aux = v} in
(*  Printf.eprintf "\t%s adding %s: %s\n"
    (Label.to_string l) (Node.print (N_enode n)) (print_v v);*)
  B.snoc b (N_enode n)

let new_labeled_block (l: Label.label) : opened =
  let h = Node.N_label l in
(*  Printf.eprintf "\tStarting new labeled block: %s\n" (Node.print h);*)
  B.join_head h B.empty

let new_block () : Label.label * opened =
  let l = Label.fresh_label () in
  l, new_labeled_block l

let end_block (b: opened) (l: Label.label list) : closed =
  let t = Node.N_jumps l in
(*  Printf.eprintf "\tEnding block with: %s\n" (Node.print t);*)
  B.join_tail b t

(* The context for generating the CFG is:
 * . an environment containing some constant bound variables
 *   (e.g. from the standard library), which are excluded from the use
 *   sets for efficiency.
 * . the accumulated set of closed blocks generated so far
 * . the current open block into which the next node should be added
 *)
type ctx = Bindings.t * closed list * opened

let rec add_stmt (ctx: ctx) (s: (typ, varid) stmt) : ctx =
  let bound, closed, b = ctx in
  match s.stmt with
    | S_assign ({expr = E_var v; _}, e) ->
        let ig = fst (Location.value v), Location.loc v in
        let l = snd (Location.value v), None, ig in
        let b = add_binding_assign bound b l e in
        bound, closed, b
    | S_assign ({expr = E_field ({expr = E_var v; _}, f); _}, e) ->
        let ig = fst (Location.value v), s.stmt_loc in
        let l = snd (Location.value v), Some (Location.value f), ig in
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

let add_gnode (b: opened) gn loc =
  let l = B.entry_label b in
  let v = {node_use = Bindings.empty; node_def = Bindings.empty, l} in
  let g = {gnode = gn; gnode_loc = loc; gnode_aux = v} in
(*  Printf.eprintf "\t%s adding %s\n" (Label.to_string l) (Node.print (N_gnode g));*)
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
    | RX_empty | RX_literals _ | RX_wildcard ->
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
        wrap (RE_seq_flat (List.map lift_regexp rxs))

(* A helper to extract the record info for the synthesized attributes
 * of a non-terminal from a typing environment *)
let get_synth_recinfo (tenv: TE.environment) (nt: string) =
  match TE.lookup_non_term tenv (NName nt) with
    | Some (_, _, nts) ->
        (match nts with
           | NTT_type (_, r)   -> r
           | NTT_record (_, r) -> !r)
    | None -> None


(* The control flow semantics during parsing require that all
 * assignment side-effects performed after a choice point along an
 * execution path for a production rule are undone or rewound when a
 * parse failure rewinds execution back to that choice point.  From
 * the point of view of the initialization analysis, this is
 * equivalent to a control-flow that does not have any failure paths.
 * In other words, we need to ensure that all *purely* successful
 * paths for a production rule end with all uninitialized attributes
 * being initialized.
 *)

let rec add_rule_elem
          (tenv: TE.environment)
          (ctx: ctx)
          (r: (typ, varid) rule_elem)
        : ctx =
  let env, closed, b = ctx in
  let pack b =
    env, closed, b in
  let mk_bitvector_ident () =
    Location.mk_loc_val "bitvector" r.rule_elem_loc in
  match r.rule_elem with
    | RE_regexp {regexp = RX_literals _; _}
    | RE_regexp {regexp = RX_wildcard; _} ->
        pack (add_gnode b GN_regexp r.rule_elem_loc)
    | RE_regexp rx ->
        let r' = lift_regexp rx in
        add_rule_elem tenv ctx r'
    | RE_non_term (id, oias) ->
        let b = match oias with
            | None -> b
            | Some ias ->
                List.fold_left (fun b (_, _, e) ->
                    add_expr env b e
                  ) b ias in
        pack (add_gnode b (GN_type id) r.rule_elem_loc)
    (* bitvectors and bitfields are treated just as types *)
    | RE_bitvector _ ->
        let bv = mk_bitvector_ident () in
        pack (add_gnode b (GN_type bv) r.rule_elem_loc)
    | RE_bitfield t ->
        pack (add_gnode b (GN_type t) r.rule_elem_loc)
    | RE_constraint e
    | RE_set_view e ->
        pack (add_expr env b e)
    | RE_action {action_stmts = ss, oe; _}->
        let env, closed, b = List.fold_left add_stmt ctx ss in
        let b = match oe with
            | None -> b
            | Some e -> add_expr env b e in
        env, closed, b
    | RE_named (n, r') ->
        (* [n] will only be defined after [r'] executes *)
        let env, closed, b = add_rule_elem tenv ctx r' in
        let p = pattern_of_var n r.rule_elem_loc r.rule_elem_aux in
        let b = add_pattern env b p in
        env, closed, b
    | RE_seq rs | RE_seq_flat rs ->
        List.fold_left (fun ctx r -> add_rule_elem tenv ctx r) ctx rs
    | RE_choice rs ->
        (* This introduces a branch point, so we need to terminate
         * this block with jumps to each of the blocks that start the
         * choices [rs].  All the choices need a common continuation,
         * so allocate a block for it. *)
        let cl, cb = new_block () in
        let ls, closed, env =
          List.fold_left (fun (ls, closed, env) r ->
              (* Allocate a new block to start this choice. *)
              let l, b = new_block () in
              let ctx = env, closed, b in
              let env, closed, b = add_rule_elem tenv ctx r in
              (* jump to the common continuation *)
              let c = end_block b [cl] in
              l :: ls, c :: closed, env
            ) ([], closed, env) rs in
        (* terminate the current block with a jump to the choices *)
        let c = end_block b ls in
        (* resume from the common continuation *)
        env, c :: closed, cb
    | RE_star (r', Some e) when is_non_zero e ->
        (* The count [e] is evaluated before [r'] is matched. For
         * non-zero bounds, we have straight line execution.
         *)
        let b   = add_expr env b e in
        let ctx = env, closed, b in
        add_rule_elem tenv ctx r'
    | RE_star (r', Some e)
    | RE_map_views (e, r') ->
        (* If we can't statically determine that [e] is always
         * non-zero for RE_star or non-empty for RE_map_views, we
         * conservatively assume that they could be zero or empty,
         * and create a branch point for the case that [r'] may not
         * execute. *)
        let b = add_expr env b e in
        (* The below logic is similar to the RE_star (r', None) case. *)
        let cl, cb = new_block () in
        let bl, bb = new_block () in
        (* End the current block with these two as possible
         * continuations *)
        let c = end_block b [bl; cl] in
        let ctx = env, c :: closed, bb in
        let env, closed, bb = add_rule_elem tenv ctx r' in
        (* insert a jump to the continuation *)
        let c = end_block bb [cl] in
        env, c :: closed, cb
    | RE_star (r', None)
    | RE_opt r' ->
        (* These both create a branch point, since r' may not execute,
         * and we could continue with the subsequent rule element.
         * Allocate a block for that continuation, and for [r']. *)
        let cl, cb = new_block () in
        let bl, bb = new_block () in
        (* End the current block with these two as possible
         * continuations *)
        let c = end_block b [bl; cl] in
        let ctx = env, c :: closed, bb in
        let env, closed, bb = add_rule_elem tenv ctx r' in
        (* insert a jump to the continuation *)
        let c = end_block bb [cl] in
        env, c :: closed, cb
    | RE_epsilon
    | RE_align _
    | RE_pad _ ->
        (* these are nops *)
        ctx
    | RE_at_pos (e, r') | RE_at_view (e, r') ->
        (* [e] is evaluated before [r'] is matched *)
        let b = add_expr env b e in
        let ctx = env, closed, b in
        add_rule_elem tenv ctx r'

(* A CFG for a production rule, and its final exit label *)
let rule_to_cfg
      (tenv: TE.environment)
      (env: Bindings.t)
      (ntd: (typ, varid) non_term_defn)
      (r: (typ, varid) rule)
    : Label.label * (Block.c, Block.c, v) G.graph * Label.label =
  (* lookup type info for the non-terminal *)
  let ntnm = Location.value ntd.non_term_name in
  let nti, _, _ = match TE.lookup_non_term tenv (NName ntnm) with
      | Some t -> t
      | None   -> assert false in
  (* The cfg needs an entry label and block, which will contain the
   * setup for the rule, viz. the binding for the non-terminal itself
   * (if present), and the attributes bindings and temporaries.
   *)
  let entry_lbl = Label.fresh_label () in
  let b = new_labeled_block entry_lbl in
  (* add inherited attributes *)
  let b = List.fold_left (fun b (ia, _, _) ->
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
  (* add any initialized synthesized attributes *)
  let b = match ntd.non_term_syn_attrs with
      | ALT_type _ -> b
      | ALT_decls ds when List.length ds = 0 -> b
      | ALT_decls ds ->
          let v =
            (match ntd.non_term_varname with
               | None ->
                   (* Could assert here, since this should have been
                    * checked before we got here. *)
                   let err =
                     Unnamed_attributed_nonterminal ntd.non_term_name in
                   raise (Error err)
               | Some v -> v) in
          let v  = Location.value v in
          let vn = fst v in
          let v  = snd v in
          List.fold_left (fun b (f, _, _, oe) ->
              match oe with
                | None   -> b
                | Some e ->
                    let l =
                      let ig = vn, Location.loc f in
                      v, Some (Location.value f), ig in
                    add_binding_assign env b l e
            ) b ds in
  (* add rule temporaries *)
  let b = List.fold_left (fun b (tv, _, te) ->
              let loc = Location.loc tv in
              let p = pattern_of_var tv loc te.expr_aux in
              add_pattern env b p
            ) b r.rule_temps in
  (* the initial context *)
  let ctx = env, [], b in
  (* add the rule elements *)
  let _, closed, b =
    List.fold_left (add_rule_elem tenv) ctx r.rule_rhs in
  (* terminate the last block with a jump to an exit label. *)
  let exit_lbl = Label.fresh_label () in
  let c = end_block b [exit_lbl] in
  (* construct the graph body *)
  let body = List.fold_left D.add_block D.empty (c :: closed) in
  (* and the graph itself *)
  let g = G.from_body body in
  (* return the graph, and the entry/exit labels *)
  entry_lbl, g, exit_lbl

module FB = MkFactBase (IVLattice)
module VA = MkAnalysis (G) (FB)

let print_fbase fb =
  Label.LabelMap.iter (fun l b ->
      Printf.eprintf "  fact@%s: %s\n"
        (Label.to_string l) (IVLattice.print b)
    ) fb
(* node transfer functions *)

let tr_co (type v)
      (n: (Block.c, Block.o, v) B.node)
      (fb: Block.c VA.facts)
    : Block.o VA.facts =
  match n, fb with
    | N_label l, Facts_closed fb ->
        (* for this analysis, entry labels should always be present in
         * the factbase *)
        (match FB.lookup fb l with
           | Some f -> Facts_open f
           | None   -> assert false)
    | _ ->
        (* this should not be needed *)
        assert false

let tr_oc (type v)
      (n: (Block.o, Block.c, v) B.node)
      (f: Block.o VA.facts)
    : Block.c VA.facts =
  match n, f with
    | N_jumps js, Facts_open f ->
        let facts = List.map (fun j -> (j, f)) js in
        Facts_closed (FB.mk_factbase facts)
    | _, _ ->
        (* this should not be needed *)
        assert false

let tr_oo
      (n: (Block.o, Block.o, v) B.node)
      (f: Block.o VA.facts)
    : Block.o VA.facts =
  let check_use (inits: ReachingDefns.t) (uses: Bindings.t) loc =
    (* All [u] in [uses] should be in the initialized set [inits] *)
    Bindings.iter (fun b ->
        if   ReachingDefns.possibly_undefined b inits
        then raise (Error (Use_of_uninit_var (b, loc)))
      ) uses in
  (* add defs to outgoing set of initvars after checking uses *)
  match f with
    | Facts_open f ->
        let out = match n with
            | N_enode e ->
                let use    = e.enode_aux.node_use in
                let def, l = e.enode_aux.node_def in
                check_use f use e.enode_loc;
                ReachingDefns.define def l f
            | N_gnode g ->
                let use    = g.gnode_aux.node_use in
                let def, l = g.gnode_aux.node_def in
                check_use f use g.gnode_loc;
                ReachingDefns.define def l f
            | _ ->
                (* this should not be needed *)
                assert false in
(*        Printf.eprintf
          " transfer: @node %s: {%s} -> {%s}\n"
          (Node.print n) (IVLattice.print f) (IVLattice.print out);*)
        Facts_open out

    | Facts_closed _ ->
        assert false

let fwd_transfer : v VA.fwd_transfer =
  (tr_co, tr_oo, tr_oc)

(* build up the base set of initialized variables:
 * . constants and functions from the prelude
 * . constants and functions defined in the spec
 *)
let build_init_bindings (init_venv: VEnv.t) (tspec: (typ, varid) program) =
  let mk_elem v =
    let loc = Location.loc v in
    let n, vid = Location.value v in
    vid, None, (n, loc) in
  let init = VEnv.fold_left (fun init v ->
                 Bindings.add (mk_elem v) init
               ) Bindings.empty init_venv in
  List.fold_left (fun init d ->
      match d with
        | Decl_types _ | Decl_format _ ->
            init
        | Decl_const c ->
            Bindings.add (mk_elem c.const_defn_ident) init
        | Decl_fun f ->
            Bindings.add (mk_elem f.fun_defn_ident) init
        | Decl_recfuns r ->
            List.fold_left (fun e f ->
                Bindings.add (mk_elem f.fun_defn_ident) e
              ) init r.recfuns
    ) init tspec.decls

(* check whether an attribute or record field is initialized *)

(* check the rules for a non-terminal *)
let check_non_term (tenv: TE.environment) (init_env: Bindings.t) ntd =
  (*  Printf.eprintf "checking %s:\n" (Location.value ntd.non_term_name);*)
  let rn = ref 0 in
  List.iter (fun r ->
(*      Printf.eprintf "  building cfg for rule %d:\n" !rn;*)
      (* get the CFG for the rule *)
      let entry, cfg, exit = rule_to_cfg tenv init_env ntd r in
(*      Printf.eprintf
        "  built cfg for rule %d with entry %s and exit %s\n"
        !rn (Label.to_string entry) (Label.to_string exit);*)
      incr rn;
      (* set up the initial factbase: at the entry label, we only
       * have uninitialized synthesized attributes, and no initialized
       * variables (since we've pruned all entries from the prelude
       * when constructing the CFG) *)
      let syn_attrs =
        let ntnm = Location.value ntd.non_term_name in
        let recinfo = get_synth_recinfo tenv ntnm in
        match recinfo, ntd.non_term_varname with
          | None, _
          | Some (TE.{fields = []; _}), _ ->  (* no synthesized attributes *)
              None
          | Some _, None ->
              (* Initialized attributes are best modeled as
               * assignments in which the lhs is a field indexed
               * variable.  If the non-terminal is not named, this is
               * not possible; and any non-initialized attributes
               * cannot be assigned.  For simplicity, just require
               * that a non-terminal with synthesized attributes must
               * use a local name. *)
              let err =
                Unnamed_attributed_nonterminal ntd.non_term_name in
              raise (Error err)
          | Some (TE.{fields = fs; _}), Some v ->
              Some (v, fs) in
      let init_fbase =
        let reaching_defs =
          match syn_attrs with
            | None ->
                ReachingDefns.empty
            | Some (v, fs) ->
                (* create undefined bindings for each attribute *)
                List.fold_left (fun rd (attr, _) ->
                    let lc = Location.loc v in
                    let vn = fst (Location.value v) in
                    let v  = snd (Location.value v) in
                    let b  = v, Some (Location.value attr), (vn, lc) in
                    ReachingDefns.add (b, None) rd
                  ) ReachingDefns.empty fs in
        FB.mk_factbase [entry, reaching_defs] in
(*      Printf.eprintf "init_fbase:\n";
      print_fbase init_fbase;*)
      let init_fbase = VA.Facts_closed init_fbase in
      (* call the forward analysis to get final factbase at [exit] *)
      let exit_fbase, _opt_factmap =
        VA.fwd_analysis init_fbase (JustC [entry]) cfg fwd_transfer in
      (* collect info on assignments of synthesized attributes *)
      match syn_attrs with
        | None ->
            ()
        | Some (v, fs) ->
            let loc = Location.loc v in
            let vn  = fst (Location.value v) in
            let v   = snd (Location.value v) in
            (* get the factbase at exit *)
            let exit_fbase = match exit_fbase with
                | VA.Facts_closed fb -> fb
                | VA.Facts_open _ -> assert false in
(*            Printf.eprintf "exit_fbase:\n";
            print_fbase exit_fbase;*)
            let exit_fact = match FB.lookup exit_fbase exit with
                | None -> assert false
                | Some f -> f in
            (* ensure all synthesized attributes are initialized at exit *)
            List.iter (fun (f, t) ->
                let f = Location.value f in
                let attr = v, Some f, (vn, loc) in
(*                Printf.eprintf " init-check for %s:\n" (binding_to_string attr);*)
                if   ReachingDefns.possibly_undefined attr exit_fact
                then
                  (* If the attribute has a record type, then it can
                   * be considered initialized if all its fields are
                   * initialized. *)
                  let is_inited =
                    match t.type_expr with
                      | TE_tapp ({type_expr = TE_tvar r; _}, _) ->
                          let rn = Location.value r in
                          (match TE.get_record_info tenv (TName rn) with
                             | None ->
                                 false
                             | _    ->
                                 true
                          )
                      | _ ->
                          false in
                  if not is_inited then
                    let err =
                      Unassigned_attribute (ntd.non_term_name, f, r.rule_loc) in
                    raise (Error err)
              ) fs
    ) ntd.non_term_rules

(* entry into this module *)
let check_spec init_envs (tenv: TE.environment) (tspec: (typ, varid) program) =
  let _, init_venv = init_envs in
  let init = build_init_bindings init_venv tspec in
  List.iter (fun d ->
      match d with
        | Decl_types _ | Decl_fun _ | Decl_recfuns _ | Decl_const _ -> ()
        | Decl_format f ->
            List.iter (fun fd ->
                check_non_term tenv init fd.format_decl
              ) f.format_decls
    ) tspec.decls
