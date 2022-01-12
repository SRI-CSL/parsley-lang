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
open Misc
open Ast
open TypingExceptions
open Pattern_utils

(** Adapted from the algorithm in
    'Warnings for pattern matching', by Luc Maranget.
    Journal of Functional Programming, Volume 17, Issue 3, May 2007. *)

(* create the most general instance of the constructor pattern *)
let mk_head_instance p =
  match p.pattern with
    | P_wildcard | P_var _ ->
        (* these are not constructors *)
        assert false
    | P_literal _ ->
        p
    | P_variant ((typ, constr), ps) ->
        let ps' =
          List.map (fun p -> {p with pattern = P_wildcard}) ps in
        {p with pattern = P_variant ((typ, constr), ps')}

let pick_missed_int il =
  let module IntSet = Set.Make(Nativeint) in
  let iset = IntSet.of_list (List.map Nativeint.of_int il) in
  let rec loop i =
    if IntSet.mem i iset
    then loop (Nativeint.succ i)
    else i in
  Nativeint.to_int (loop Nativeint.zero)

let pick_missed_string sl =
  let sset = StringSet.of_list sl in
  let rec loop s =
    if StringSet.mem s sset
    then loop (String.concat s ["a"])
    else s in
  loop ""

let pick_missed_bitvector bvl width =
  let bvs = BVSet.of_list (List.map bv_to_int bvl) in
  let max = Int64.shift_left Int64.one width in
  let rec loop i =
    assert (i != max);
    if BVSet.mem i bvs
    then loop (Int64.succ i)
    else int_to_bv i width in
  loop Int64.zero

(* picks a constructor missing from the signature *)
let pick_missed_constructor tenv signature =
  let p = List.hd signature in
  match p.pattern with
    | P_wildcard | P_var _ ->
        assert false
    | P_literal PL_unit ->
        assert false
    | P_literal (PL_int _) ->
        let l =
          List.map (function
              | {pattern = P_literal (PL_int i); _} -> i
              | _ -> assert false
            ) signature in
        let i = pick_missed_int l in
        {p with pattern = P_literal (PL_int i)}
    | P_literal (PL_bytes _) ->
        let l =
          List.map (function
              | {pattern = P_literal (PL_bytes s); _} -> s
              | _ -> assert false
            ) signature in
        let s = pick_missed_string l in
        {p with pattern = P_literal (PL_bytes s)}
    | P_literal (PL_bool b) ->
        ignore (List.map
                  (function
                   | {pattern = P_literal (PL_bool b'); _} -> assert (b = b')
                   | _ -> assert false
                  ) signature);
        {p with pattern = P_literal (PL_bool (not b))}
    | P_literal (PL_bit b) ->
        ignore (List.map
                  (function
                   | {pattern = P_literal (PL_bit b'); _} -> assert (b = b')
                   | _ -> assert false
                  ) signature);
        {p with pattern = P_literal (PL_bit (not b))}
    | P_literal (PL_bitvector bv) ->
        let l =
          List.map (function
              | {pattern = P_literal (PL_bitvector bv); _} -> bv
              | _ -> assert false
            ) signature in
        let v = pick_missed_bitvector l (List.length bv) in
        {p with pattern = P_literal (PL_bitvector v)}
    | P_variant ((typ, _), ps) ->
        let cs =
          List.map (fun p ->
              match p.pattern with
                | P_variant ((typ', c), _) ->
                    assert (Location.value typ' = Location.value typ);
                    c
                | _ ->
                    assert false
            ) signature in
        let unused = unused_constructors tenv typ cs in
        assert (not (StringSet.is_empty unused));
        let c = Location.mk_ghost (StringSet.choose unused) in
        let p = {p with pattern = P_variant ((typ, c), ps)} in
        mk_head_instance p

type pmat =
  ((MultiEquation.crterm, TypeInfer.varid) pattern list * unit) list

let rec check_matrix tenv (mat: pmat) cols wildcard =
  match mat with
    | [] ->
        (* the base case where mat has zero rows *)
        Some (repeat wildcard cols)
    | (p, _) :: rest when p = [] ->
        (* the base case where mat has zero columns *)
        assert (cols = 0);
        List.iter (fun (p, _) -> assert (List.length p = 0)) rest;
        None
    | (p, _) :: _ ->
        let roots = roots tenv (first_col mat) in
        let signature = List.map fst roots in
        if is_complete_sig tenv signature
        then begin
            (* We could fold and terminate early for efficiency, but
             * make an exhaustive scan instead for now to debug the
             * algorithm. *)
            let insts =
              List.map (fun (root, arity) ->
                  let wild = {root with pattern = P_wildcard} in
                  let smat = specialize_mat tenv mat root in
                  let inst =
                    check_matrix tenv smat (arity + cols - 1) wild in
                  (root, inst)
                ) roots in
            List.fold_left (fun acc (root, inst) ->
                match (acc, inst) with
                  | Some _, _  ->
                      (* we've already found a missed instance, skip inst *)
                      acc
                  | None, None ->
                      (* nothing useful from this sub-instance *)
                      acc
                  | None, Some ps ->
                      (* we've found our first missed sub-instance *)
                      Some ((mk_head_instance root) :: ps)
              ) None insts
          end
        else begin
            let p = List.hd p in
            let wild = {p with pattern = P_wildcard} in
            let inst =
              check_matrix tenv (default_mat mat) (cols - 1) wild in
            match inst with
              | None ->
                  (* no missed instances *)
                  None
              | Some ps ->
                  (* found a missed instance *)
                  if List.length signature = 0
                  then Some (wild :: ps)
                  else Some (pick_missed_constructor tenv signature :: ps)
          end

(** [check_exhaustiveness tenv col] checks the pattern column [col] for
    exhaustiveness, where the column is extracted from a case
    expression or statement *)
let check_exhaustiveness tenv col =
  match col with
    | [] ->
        ()
    | p :: _ ->
        let wild = {p with pattern = P_wildcard} in
        let mat = List.map (fun p -> [p], ()) col in
        (match check_matrix tenv mat 1 wild with
           | None ->
               ()
           | Some exs ->
               assert (List.length exs > 0);
               let ex = AstPrinter.sprint_pattern (List.hd exs) in
               raise (Error (UnmatchedPattern (p.pattern_loc, ex)))
        )

(** [check_usefulness tenv col] checks whether each row in the pattern
   column [col] is useful *)
let check_usefulness tenv col =
  ignore (
    List.fold_left (fun acc c ->
        let mat = List.map (fun p -> [p], ()) acc in
        (match check_matrix tenv mat 1 c with
           | None ->
               raise (Error (UselessPattern c.pattern_loc))
           | Some exs ->
               assert (List.length exs > 0);
               acc @ [c])
      ) [] col
    )

let check_pattern tenv col : unit =
  check_exhaustiveness tenv col;
  check_usefulness tenv col

(* The ~~ operator constrains the data constructors for expressions,
   which can cause false exhaustiveness errors for when those
   constrained expressions are later used as the values of let binding
   patterns.  This is handled by keeping track of these constraints,
   and checking at let binding patterns whether their values have such
   a constraint.  If so, the top-level constructor is matched; if not,
   the pattern is added to the set to be checked.

   The constraint context is initialized per rule, updated at match
   constraints, and looked up when processing let expressions and
   statements.
*)

(* map from (unwrapped) expressions to their (unwrapped) binding constructors *)
module ExpConstraint =
  Map.Make(struct type t = (unit, unit) expr
                  let compare = compare
           end)

let add_constraint ctx e c =
  let e = AstUtils.unwrap_exp e in
  let c = AstUtils.unwrap_constructor c in
  let cs = ExpConstraint.find_opt e ctx in
  let cs = match cs with
      | None    -> [c]
      | Some cs -> c :: cs in
  ExpConstraint.add e cs ctx

let has_constraint ctx e c =
  let e = AstUtils.unwrap_exp e in
  let c = AstUtils.unwrap_constructor c in
  match ExpConstraint.find_opt e ctx with
    | None    -> false
    | Some cs -> List.mem c cs

(** [extract_expr_pats expr] extracts the patterns used in all the
    subexpressions of [expr], using the various [descend_*] helpers *)
let rec extract_expr_pats ctx expr =
  descend_expr (ctx, []) expr

and descend_expr (ctx, acc) e =
    match e.expr with
      | E_var _
      | E_literal _
      | E_mod_member _ ->
          (ctx, acc)
      | E_unop (_, e)
      | E_field (e, _)
      | E_cast (e, _) ->
          descend_expr (ctx, acc) e
      | E_match (e, c) ->
          let ctx', acc' = descend_expr (ctx, acc) e in
          (add_constraint ctx' e c), acc'
      | E_constr (_, es) ->
          List.fold_left descend_expr (ctx, acc) es
      | E_record fs ->
          List.fold_left (fun (ctx, acc) (_, e) ->
              descend_expr (ctx, acc) e
            ) (ctx, acc) fs
      | E_apply (f, args) ->
          List.fold_left descend_expr (ctx, acc) (f :: args)
      | E_binop (_, l, r) ->
          descend_expr (descend_expr (ctx, acc) l) r
      | E_recop (_, _, e) ->
          descend_expr (ctx, acc) e
      | E_bitrange (e, _, _) ->
          descend_expr (ctx, acc) e
      | E_case (e, bs) ->
          (* case patterns are not affected by match constraints *)
          let pmat, es = List.split bs in
          List.fold_left (fun (ctx, acc) e ->
              descend_expr (ctx, acc) e
            ) (descend_expr (ctx, pmat :: acc) e) es
      | E_let ({pattern = P_variant (c, _); _}, e, b)
           when has_constraint ctx e c ->
          (* skip check for p if e is already constrained by c *)
          descend_expr (descend_expr (ctx, acc) e) b
      | E_let (p, e, b) ->
          descend_expr (descend_expr (ctx, [p] :: acc) e) b

(** [extract_nt_pats ntd] extracts the patterns used in all the
    expressions (and subexpressions) in the production rules of the
    non-terminal definition [ntd], using the various [descend_*]
    helpers. *)

let rec extract_nt_pats ntd =
  let ctx = ExpConstraint.empty in
  let acc =
    match ntd.non_term_syn_attrs with
      | ALT_type _ ->
          []
      | ALT_decls dl ->
          List.fold_left (fun acc (_, _, _, eo) ->
              match eo with
                | None ->
                    acc
                | Some e ->
                    let _, acc = descend_expr (ctx, acc) e in
                    acc
            ) [] dl in
  List.fold_left descend_rule acc ntd.non_term_rules

and descend_rule acc r =
  (* the pattern constraint context is initialized per-rule, and only
     used in the rhs. *)
  let ctx = ExpConstraint.empty in
  let acc =
    List.fold_left (fun acc (_, _, e) ->
        snd (descend_expr (ctx, acc) e)
      ) acc r.rule_temps in
  snd (List.fold_left descend_rule_elem (ctx, acc) r.rule_rhs)

(* propagate the pattern constraint only across constraint rule elements *)
and descend_rule_elem (ctx, acc) re =
  match re.rule_elem with
    | RE_non_term (_, None)
    | RE_bitvector _
    | RE_align _
    | RE_pad _
    | RE_bitfield _
    | RE_epsilon ->
        ctx, acc
    | RE_regexp re ->
        ctx, descend_regexp ctx acc re
    | RE_action a ->
        ctx,
        snd (match a.action_stmts with
               | stmts, None ->
                   List.fold_left descend_stmt (ctx, acc) stmts
               | stmts, Some e ->
                   List.fold_left descend_stmt (descend_expr (ctx, acc) e) stmts
            )
    | RE_constraint e
    | RE_set_view e ->
        descend_expr (ctx, acc) e
    | RE_non_term (_, Some ias) ->
        ctx,
        List.fold_left (fun acc (_, _, e) ->
            snd (descend_expr (ctx, acc) e)
        ) acc ias
    | RE_named (_, re)
    | RE_star (re, None)
    | RE_opt re ->
        ctx, snd (descend_rule_elem (ctx, acc) re)
    | RE_seq res | RE_seq_flat res
    | RE_choice res ->
        ctx, snd (List.fold_left descend_rule_elem (ctx, acc) res)
    | RE_star (re, Some e)
    | RE_at_pos (e, re)
    | RE_at_view (e, re)
    | RE_map_views (e, re) ->
        ctx, snd (descend_rule_elem (descend_expr (ctx, acc) e) re)

and descend_regexp ctx acc re =
  match re.regexp with
    | RX_empty
    | RX_literals _
    | RX_wildcard
    | RX_type _
    | RX_star (_, None) ->
        acc
    | RX_star (_, Some e) ->
        snd (descend_expr (ctx, acc) e)
    | RX_opt re ->
        descend_regexp ctx acc re
    | RX_choice res
    | RX_seq res ->
        List.fold_left (descend_regexp ctx) acc res

and descend_stmt (ctx, acc) s =
  match s.stmt with
    | S_assign (e, e') ->
        descend_expr (descend_expr (ctx, acc) e) e'
    | S_let ({pattern = P_variant (c, _); _} as p, e, ss) ->
        (* skip check for p if e is already constrained by c *)
        let acc' = if has_constraint ctx e c
                   then acc
                   else [p] :: acc in
        List.fold_left descend_stmt (descend_expr (ctx, acc') e) ss
    | S_let (p, e, ss) ->
        List.fold_left descend_stmt (descend_expr (ctx, [p] :: acc) e) ss
    | S_case (e, bs) ->
        let pmat, ss = List.split bs in
        List.fold_left (fun (ctx, acc) s ->
            List.fold_left descend_stmt (ctx, acc)  s
          ) (descend_expr (ctx, pmat :: acc) e) ss

let check_patterns tenv (spec: (MultiEquation.crterm, TypeInfer.varid) Ast.program)  =
  let ctx = ExpConstraint.empty in
  let check_fun f =
    List.iter
      (check_pattern tenv)
      (snd (extract_expr_pats ctx f.fun_defn_body)) in
  List.iter (function
      | Decl_types _ | Decl_const _ ->
          ()
      | Decl_fun f ->
          check_fun f
      | Decl_recfuns r ->
          List.iter check_fun r.recfuns
      | Decl_format f ->
          List.iter (fun fd ->
              List.iter (check_pattern tenv) (extract_nt_pats fd.format_decl)
            ) f.format_decls
    ) spec.decls
