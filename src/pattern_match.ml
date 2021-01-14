open Ast

let check_pats _ =
  ()

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
          List.fold_left (fun acc (p, e) ->
              descend_expr(p :: acc) e
            ) (descend_expr acc e) bs
      | E_let (p, e, b) ->
          descend_expr (descend_expr (p :: acc) e) b

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
        List.fold_left descend_stmt (descend_expr (p :: acc) e) ss
    | S_case (e, bs) ->
        List.fold_left (fun acc (p, ss) ->
            List.fold_left descend_stmt (p :: acc) ss
          ) (descend_expr acc e) bs

let check_patterns spec =
  List.iter (function
      | Decl_types _ ->
          ()
      | Decl_fun f ->
          List.iter check_pats (extract_expr_pats f.fun_defn_body)
      | Decl_format f ->
          List.iter (fun fd ->
              List.iter check_pats (extract_nt_pats fd.format_decl)
            ) f.format_decls
    ) spec.decls
