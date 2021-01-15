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
      TypeConv.canonicalize_dcon
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

(** [check_completeness tenv typ cs] checks whether the list [cs] of
    constructors of type [typ] contains all the constructors of the
    type. *)
let check_completeness tenv typ cs =
  StringSet.is_empty (unused_constructors tenv typ cs)

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
               check_completeness tenv t cs
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

(** [extract_expr_pats expr] extracts the patterns used in all the
    subexpressions of [expr], using the various [descend_*] helpers *)
let rec extract_expr_pats expr =
  descend_expr [] expr

and descend_expr acc e =
    match e.expr with
      | E_var _
      | E_literal _
      | E_mod_member _ ->
          acc
      | E_unop (_, e)
      | E_match (e, _, _)
      | E_field (e, _)
      | E_cast (e, _) ->
          descend_expr acc e
      | E_constr (_, _, es) ->
          List.fold_left descend_expr acc es
      | E_record fs ->
          List.fold_left (fun acc (_, e) ->
              descend_expr acc e
            ) acc fs
      | E_apply (f, args) ->
          List.fold_left descend_expr acc (f :: args)
      | E_binop (_, l, r) ->
          descend_expr(descend_expr acc l) r
      | E_case (e, bs) ->
          let pmat, es = List.split bs in
          List.fold_left (fun acc e ->
              descend_expr acc e
            ) (descend_expr (pmat :: acc) e) es
      | E_let (p, e, b) ->
          descend_expr (descend_expr ([p] :: acc) e) b

(** [extract_nt_pats ntd] extracts the patterns used in all the
    expressions (and subexpressions) in the production rules of the
    non-terminal definition [ntd], using the various [descend_*]
    helpers. *)
let rec extract_nt_pats ntd =
  let acc =
    match ntd.non_term_syn_attrs with
      | ALT_type _ -> []
      | ALT_decls dl ->
          List.fold_left (fun acc (_, _, eo) ->
              match eo with
                | None -> acc
                | Some e -> descend_expr acc e
            ) [] dl in
  List.fold_left descend_rule acc ntd.non_term_rules

and descend_rule acc r =
  let acc =
    List.fold_left (fun acc (_, _, e) ->
        descend_expr acc e
      ) acc r.rule_temps in
  List.fold_left descend_rule_elem acc r.rule_rhs

and descend_rule_elem acc re =
  match re.rule_elem with
    | RE_non_term (_, None)
    | RE_epsilon ->
        acc
    | RE_regexp re ->
        descend_regexp acc re
    | RE_action a ->
        (match a.action_stmts with
           | stmts, None ->
               List.fold_left descend_stmt acc stmts
           | stmts, Some e ->
               List.fold_left descend_stmt (descend_expr acc e) stmts
        )
    | RE_constraint e ->
        descend_expr acc e
    | RE_non_term (_, Some ias) ->
        List.fold_left (fun acc (_, e) ->
            descend_expr acc e
          ) acc ias
    | RE_named (_, re)
    | RE_star (re, None)
    | RE_opt re ->
        descend_rule_elem acc re
    | RE_seq res
    | RE_choice res ->
        List.fold_left descend_rule_elem acc res
    | RE_star (re, Some e)
    | RE_at_pos (e, re)
    | RE_at_buf (e, re)
    | RE_map_bufs (e, re) ->
        descend_rule_elem (descend_expr acc e) re

and descend_regexp acc re =
  match re.regexp with
    | RX_literals _
    | RX_wildcard
    | RX_type _
    | RX_star (_, None) ->
        acc
    | RX_star (_, Some e) ->
        descend_expr acc e
    | RX_opt re ->
        descend_regexp acc re
    | RX_choice res
    | RX_seq res ->
        List.fold_left descend_regexp acc res

and descend_stmt acc s =
  match s.stmt with
    | S_assign (e, e') ->
        descend_expr (descend_expr acc e) e'
    | S_let (p, e, ss) ->
        List.fold_left descend_stmt (descend_expr ([p] :: acc) e) ss
    | S_case (e, bs) ->
        let pmat, ss = List.split bs in
        List.fold_left (fun acc s ->
            List.fold_left descend_stmt acc s
          ) (descend_expr (pmat :: acc) e) ss

let check_patterns tenv spec =
  List.iter (function
      | Decl_types _ ->
          ()
      | Decl_fun f ->
          List.iter (check_pattern tenv) (extract_expr_pats f.fun_defn_body)
      | Decl_format f ->
          List.iter (fun fd ->
              List.iter (check_pattern tenv) (extract_nt_pats fd.format_decl)
            ) f.format_decls
    ) spec.decls
