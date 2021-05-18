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
open TypingEnvironment
open TypingExceptions

(** Adapted from the algorithm in
    'Warnings for pattern matching', by Luc Maranget.
    Journal of Functional Programming, Volume 17, Issue 3, May 2007. *)

let repeat p n =
  let rec iter n acc =
    if n = 0 then acc
    else iter (n - 1) (p :: acc) in
  iter n []

let arity tenv typ constr =
  let arity, _, _ =
    let dcid =
      AstUtils.canonicalize_dcon
        (Location.value typ) (Location.value constr) in
    lookup_datacon tenv (Location.loc typ) (DName dcid) in
  arity

(** [default_mat m] computes the default matrix for a given pattern
    matrix [m]. *)
let default_mat m =
  let default_row ps =
    match ps with
      | p :: rest ->
          (match p.pattern with
             | P_wildcard  | P_var _     -> Some rest
             | P_literal _ | P_variant _ -> None)
      | [] -> assert false in
  List.fold_right (fun p acc ->
      match default_row p with
        | None   -> acc
        | Some r -> r :: acc
    ) m []

(** [specialize_row_constr tenv (typ, constr) ps] computes the
    specialized version of a pattern row [ps] with respect to the
    constructor [constr] of type [typ]. *)
let specialize_row_constr tenv (typ, constr) ps =
  let arity = arity tenv typ constr in
  match ps with
    | p :: rest ->
        (match p.pattern with
           | P_wildcard
           | P_var _ ->
               let p' = { p with pattern = P_wildcard } in
               Some (repeat p' arity)
           | P_variant ((typ', constr'), ps)
                when Location.value typ' = Location.value typ ->
               if Location.value constr' = Location.value constr
               then (
                 assert (List.length ps = arity);
                 Some (ps @ rest)
               )
               else None
           | P_literal _ ->
               (* Type-check should forbid this. *)
               assert false
           | P_variant ((typ', _), _) ->
               (* Type-check should forbid this assertion failing. *)
               assert (Location.value typ' == Location.value typ);
               None)
    | [] ->
        assert false

(** [specialize_row_literal lit ps] computes the specialized version
    of a pattern row [ps] with respect to the constructor
    corresponding to the literal [lit]. *)
let specialize_row_literal lit ps =
  match ps with
    | p :: rest ->
        (match p.pattern with
           | P_wildcard
           | P_var _ ->
               Some rest
           | P_literal l when l = lit ->
               Some rest
           | P_literal _ ->
               None
           | P_variant _ ->
               (* Type-check should forbid this. *)
               ignore (assert false);
               None)
    | [] ->
        assert false

let specialize_mat tenv mat p =
  let filter mat =
    List.fold_right (fun r acc ->
        match r with
          | None   -> acc
          | Some r -> r :: acc
      ) mat [] in
  match p.pattern with
    | P_wildcard | P_var _ ->
        (* these are not constructors *)
        assert false
    | P_literal l ->
        filter (List.map (specialize_row_literal l) mat)
    | P_variant ((typ, constr), _) ->
        filter (List.map (specialize_row_constr tenv (typ, constr)) mat)

(** [unused_constructors tenv typ cs] computes the set of unused
    constructors of type [typ] given a list [cs] of used
    constructors. *)
let unused_constructors tenv typ cs =
  let tn = Location.value typ in
  let adti =
    match lookup_adt tenv (TName tn) with
      | None -> assert false
      | Some i -> i in
  let dcons = match adti.adt with
      | Variant dcons -> dcons
      | Record _ -> assert false in
  let dcons =
    List.fold_left (fun acc (DName c, _) ->
        StringSet.add c acc
      ) StringSet.empty dcons in
  List.fold_left (fun acc c ->
      StringSet.remove (Location.value c) acc
    ) dcons cs

(** [check_variant_completeness tenv typ cs] checks whether the list
    [cs] of constructors of type [typ] contains all the constructors
    of the type. *)
let check_variant_completeness tenv typ cs =
  StringSet.is_empty (unused_constructors tenv typ cs)

(* helpers for bitvector patterns *)

let bv_to_int bv =
  List.fold_left (fun i b ->
      let i = Int64.shift_left i 1 in
      Int64.add i (if b then Int64.one else Int64.zero)
    ) Int64.zero bv

let int_to_bv int width =
  let bit_to_bool i =
    Int64.logand i Int64.one == Int64.one in
  let rec iter acc cnt =
    if cnt = width
    then acc
    else let int = Int64.shift_right int cnt in
         let bit = bit_to_bool int in
         iter (bit :: acc) (cnt + 1) in
  iter [] 0

module BVSet = Set.Make(Int64)

let check_bitvector_completeness set width =
  assert (width <= 64);
  let max = Int64.shift_left Int64.one width in
  let rec check i =
    if Int64.equal i max
    then true
    else if BVSet.mem i set
    then check (Int64.succ i)
    else false in
  check Int64.zero

(** [is_complete_sig tenv roots] checks whether the root constructors
    [roots] form a complete signature for their type. *)
let is_complete_sig tenv roots =
  match roots with
    | [] ->
        false
    | p :: rest ->
        (match p.pattern with
           | P_wildcard | P_var _ ->
               (* these are not roots *)
               assert false
           | P_literal PL_unit ->
               List.iter (fun p ->
                   assert (p.pattern = P_literal PL_unit)
                 ) rest;
               true
           | P_literal (PL_string _) ->
               List.iter (fun p ->
                   match p.pattern with
                     | P_literal (PL_string _) -> ()
                     | _ -> assert false
                 ) rest;
               false
           | P_literal (PL_int _) ->
               List.iter (fun p ->
                   match p.pattern with
                     | P_literal (PL_int _) -> ()
                     | _ -> assert false
                 ) rest;
               false
           | P_literal (PL_bool b) ->
               List.fold_left (fun acc p ->
                   match p.pattern with
                     | P_literal (PL_bool b') ->
                         b != b' || acc
                     | _ -> assert false
                 ) false rest
           | P_literal (PL_bit b) ->
               List.fold_left (fun acc p ->
                   match p.pattern with
                     | P_literal (PL_bit b') ->
                         b != b' || acc
                     | _ -> assert false
                 ) false rest
           | P_literal (PL_bitvector bv) ->
               let bvs =
                 List.fold_left (fun acc p ->
                     match p.pattern with
                       | P_literal (PL_bitvector bv') ->
                           assert (List.length bv' == List.length bv);
                           BVSet.add (bv_to_int bv') acc
                       | _ -> assert false
                   )
                   (BVSet.add (bv_to_int bv) BVSet.empty)
                   rest in
               check_bitvector_completeness bvs (List.length bv)
           | P_variant ((t, c), _) ->
               let cs =
                 List.fold_left (fun acc p ->
                     match p.pattern with
                       | P_variant ((t', c'), _) ->
                           assert (Location.value t = Location.value t');
                           c' :: acc
                       | _ ->
                           assert false
                   ) [c] rest in
               check_variant_completeness tenv t cs
        )

(* extract the first column of a pattern matrix *)
let first_col mat =
  List.fold_right (fun row acc ->
      match row with
        | []     -> assert false  (* not called for base case *)
        | h :: _ -> h  :: acc
    ) mat []

(* extract the constructors from a pattern column *)
let roots tenv col =
  List.fold_right (fun p acc ->
      match p.pattern with
        | P_wildcard | P_var _ ->
            (* these are not constructors *)
            acc
        | P_literal _ ->
            (* literals have arity 0 *)
            (p, 0) :: acc
        | P_variant ((typ, constr), _) ->
            (p, arity tenv typ constr) :: acc
    ) col []

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
    | P_literal (PL_string _) ->
        let l =
          List.map (function
              | {pattern = P_literal (PL_string s); _} -> s
              | _ -> assert false
            ) signature in
        let s = pick_missed_string l in
        {p with pattern = P_literal (PL_string s)}
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

let rec check_matrix tenv mat cols wildcard =
  match mat with
    | [] ->
        (* the base case where mat has zero rows *)
        Some (repeat wildcard cols)
    | p :: rest when p = [] ->
        (* the base case where mat has zero columns *)
        assert (cols = 0);
        List.iter (fun p -> assert (List.length p = 0)) rest;
        None
    | p :: _ ->
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

(** [check_pattern tenv col] checks the pattern column [col] for
    exhaustiveness, where the column is extracted from a case
    expression or statement *)
let check_pattern tenv col =
  match col with
    | [] ->
        ()
    | p :: _ ->
        let wild = {p with pattern = P_wildcard} in
        let mat = List.map (fun p -> [p]) col in
        (match check_matrix tenv mat 1 wild with
           | None ->
               ()
           | Some exs ->
               assert (List.length exs = 1);
               let ex = AstPrinter.sprint_pattern (List.hd exs) in
               raise (Error (UnmatchedPattern (p.pattern_loc, ex)))
        )


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
          List.fold_left (fun acc (_, _, eo) ->
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
    | RE_constraint e ->
        descend_expr (ctx, acc) e
    | RE_non_term (_, Some ias) ->
        ctx,
        List.fold_left (fun acc (_, e) ->
            snd (descend_expr (ctx, acc) e)
        ) acc ias
    | RE_named (_, re)
    | RE_star (re, None)
    | RE_opt re ->
        ctx, snd (descend_rule_elem (ctx, acc) re)
    | RE_seq res
    | RE_choice res ->
        ctx, snd (List.fold_left descend_rule_elem (ctx, acc) res)
    | RE_star (re, Some e)
    | RE_at_pos (e, re)
    | RE_at_buf (e, re)
    | RE_map_bufs (e, re) ->
        ctx, snd (descend_rule_elem (descend_expr (ctx, acc) e) re)

and descend_regexp ctx acc re =
  match re.regexp with
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

let check_patterns tenv spec =
  let ctx = ExpConstraint.empty in
  List.iter (function
      | Decl_types _ ->
          ()
      | Decl_fun f ->
          List.iter
            (check_pattern tenv)
            (snd (extract_expr_pats ctx f.fun_defn_body))
      | Decl_format f ->
          List.iter (fun fd ->
              List.iter (check_pattern tenv) (extract_nt_pats fd.format_decl)
            ) f.format_decls
    ) spec.decls
