open Fmt
open Location
open Ast
open Stdlib
open Lexing

let print_string str fmt _ =  string fmt str;;

let get_pos_info pos = pos.pos_fname, pos.pos_lnum, pos.pos_cnum - pos.pos_bol

let pprint_ploc fmt l =
    let x, y, z = get_pos_info l.loc_start
  in pf fmt " Location: \n loc_start_pos: %s %d %d" x y z

let pprint_str_location fmt f =
    braces
    (concat ~sep:comma
    [(fun fmt t ->
        pf fmt "string: ";
        string fmt f.pelem);
     (fun fmt t -> pprint_ploc fmt f.ploc)])
    fmt f;;

let pprint_ident = braces (print_string "ident: " ++ pprint_str_location);;

let pprint_format_name fmt f =
    pf fmt "format_name: ";
    pprint_ident fmt f.format_name;;

let pprint_loc fmt l = pf fmt "loc: _";;
let pprint_format_loc fmt f = pprint_loc fmt f.format_loc;;
let pprint_format_decl_loc fmt f = pprint_loc fmt f.format_decl_loc;;
let pprint_format_lob fmt f = pf fmt "format_lob: xyz" ;;

let pprint_non_term_name fmt non_term_defn = pf fmt "non_term_name: "; pprint_ident fmt non_term_defn.non_term_name

let pprint_non_term_varname fmt non_term_defn =
    match non_term_defn.non_term_varname with
    | Some varname -> pf fmt "varname: "; pprint_ident fmt varname;
    | None -> pf fmt "varname: "; pf fmt "none";;

let pprint_path = brackets (list pprint_ident);;

let pprint_pattern fmt p = pf fmt "TODO: pattern"
let pprint_binop fmt b = pf fmt "TODO binop"
let pprint_unop fmt u = pf fmt "TODO unop"

let rec pprint_expr_desc fmt = function
  | E_path x -> pf fmt "E_path:"; brackets pprint_path fmt x
  | E_int x -> pf fmt "E_int: "; pf fmt "%d" x;
  | E_tuple x -> braces (list pprint_expr) fmt x
  | E_apply (x , y) -> pf fmt "E_apply:"; brackets (fun fmt _ -> pprint_expr fmt x; braces (list pprint_expr) fmt y) fmt y
  | E_unop (u, e) -> pf fmt "E_unop"; pprint_unop fmt u; pprint_expr fmt e
  | E_binop (b, e1, e2 ) -> pf fmt "binop * expr * expr"; pprint_binop fmt b; pprint_expr fmt e1; pprint_expr fmt e2;
  | E_index (e,e1) -> pf fmt "expr * expr"
  | E_literal x -> pf fmt "E_literal: "; brackets pprint_str_location fmt x
  | E_cast (e, p) -> pf fmt "E_cast:" ; brackets (fun fmt _ -> pprint_expr fmt e;
            pprint_path fmt p) fmt (e, p)
  | E_field (e, p) -> pf fmt "E-field: expr * path"; brackets (fun fmt _ -> pprint_expr fmt e; pprint_path fmt p) fmt (e, p)
  | E_case (e, pe_list) ->
          pf fmt "E_case: expr * (pattern * expr) list";
          (fun fmt (e, pe_List) -> pprint_expr fmt e;
          (list (fun fmt (p, e) -> pprint_pattern fmt p; pprint_expr fmt e)) fmt pe_list) fmt (e, pe_list)
  | E_let (p,e,e1) ->
          pf fmt "pattern * expr * expr"; pprint_pattern fmt p; pprint_expr fmt e; pprint_expr fmt e1;
  | E_constr (i, e) -> pf fmt "placeholder ie list printer"
  | E_match (e, p) -> pf fmt "placeholder (expr, path) printer"
and pprint_expr fmt x =
  pf fmt "expr: ";
  brackets
    (fun fmt t ->
       pprint_loc fmt t.expr_loc;
       pprint_expr_desc fmt t.expr)
    fmt x;;

let pprint_rule_constraint = pprint_expr

let pprint_rule_loc = pprint_loc

let pprint_rule_temps fmt x = pf fmt "rule_tmps";;

let pprint_stmt_desc fmt = function
    | S_assign (expr1, expr2) ->
        pf fmt "S assign: ";
        pprint_expr fmt expr1;
        pprint_expr fmt expr2;;
let pprint_stmt fmt t = pprint_stmt_desc fmt t.stmt

let pprint_rule_action fmt t =
    pprint_loc fmt t.action_loc ;
    pf fmt  ", ";
    (brackets (list pprint_stmt)) fmt t.action_stmts;;
let pprint_char_class fmt t = pf fmt "placeholder"

let rec pprint_rule_elem fmt rule_elem =
    pf fmt "rule elem:";
  braces
  (concat ~sep:comma
  [ (fun fmt t -> pprint_loc fmt t.rule_elem_loc);
    (fun fmt t -> pprint_rule_elem_desc fmt t.rule_elem) ])
  fmt rule_elem
  and pprint_rule_elem_desc fmt = function
      | RE_literal x -> pf fmt "RE_literal: "; pprint_str_location fmt x
      | RE_non_term (i1, i2, ie) -> pf fmt "RE_nonterm_placeholder"
      | RE_named_regex (rule_elem, ident) ->
          braces
          (fun fmt t ->
              pprint_rule_elem fmt rule_elem;
              pprint_ident fmt ident;) fmt fmt;
      | RE_constraint x -> pprint_rule_constraint fmt x
      | RE_action x -> pf fmt "RE_action: "; pprint_rule_action fmt x
      | RE_choice (x, y) -> pprint_rule_elem fmt x; pprint_rule_elem fmt y
      | RE_seq t -> brackets (list pprint_rule_elem) fmt t
      | RE_star x -> pprint_rule_elem fmt x
      | RE_plus x -> pprint_rule_elem fmt x
      | RE_opt x -> pprint_rule_elem fmt x
      | RE_cclass_repeat (ch, e) -> pprint_char_class fmt ch; pprint_expr fmt e
      | RE_nterm_repeat (i, ie_list_option, expr) -> pf fmt "placeholder"
      | RE_char_class x -> pf fmt "placeholder char class"
      | RE_epsilon -> pf fmt "RE_epsilon"

let pprint_tvar fmt t = pf fmt "tvar: "; pprint_str_location fmt t;;

let rec pprint_type_expr_desc fmt = function
  | TE_tvar x -> pf fmt "TE_tvar: "; pprint_tvar fmt x
  | TE_typeof x -> pf fmt "TE_path: ";  pprint_path fmt x
  | TE_tuple x -> pf fmt "TE_tuple: "; brackets (list pprint_type_expr) fmt x
  | TE_list x -> pf fmt "TE_list: "; pprint_type_expr fmt x
  | TE_constr (x, y) ->
          pf fmt "TE_constr: ";
          pprint_path fmt x;
          brackets (list pprint_type_expr) fmt y;
    and pprint_type_expr fmt x =
          braces
    (fun fmt t ->
        pprint_type_expr_desc fmt t.type_expr;
        pf fmt ", ";
        pprint_loc fmt t.type_expr_loc;
          ) fmt x;;

let pprint_param_decl =
    print_string "pram decl:"
     ++
    braces
    (fun fmt param_decl ->
        let ident, type_expr = param_decl.pelem in
        pprint_ident fmt ident;
        pf fmt ",";
        pprint_type_expr fmt type_expr);;

let pprint_rule_temps = print_string "rule temps: " ++ brackets (list pprint_param_decl);;

let pprint_rule =
    braces
  (concat ~sep:comma
    [(fun fmt t ->
        pf fmt "rule rhs:";
        brackets (list pprint_rule_elem) fmt t.rule_rhs;);
    (fun fmt t ->
        pf fmt "rule temps: ";
        pprint_rule_temps fmt t.rule_temps);
    (fun fmt t ->
        pf fmt "rule loc: ";
        pprint_loc fmt t.rule_loc)
  ])
;;

let pprint_non_term_inh_attrs fmt non_term_defn =
    pf fmt "non_term_rules:";
    brackets (list pprint_rule) fmt non_term_defn.non_term_rules;;


let pprint_non_term_inh_attrs fmt non_term_defn =
    pf fmt "non_term_inh_attrs: ";
    brackets (list pprint_param_decl) fmt non_term_defn.non_term_inh_attrs;;

let pprint_non_term_syn_attrs fmt non_term_defn =
    pf fmt "non_term_syn_attrs: ";
    brackets (list pprint_param_decl) fmt non_term_defn.non_term_syn_attrs;;

let pprint_non_term_rules fmt t = (brackets (list pprint_rule)) fmt t.non_term_rules;;
let pprint_non_term_loc fmt t = pprint_loc fmt t.non_term_loc;;

let pprint_non_term_defn =
    print_string "non_term_defn: " ++
    braces
    (concat ~sep:comma
    [ pprint_non_term_name;
      pprint_non_term_varname;
      pprint_non_term_inh_attrs;
      pprint_non_term_syn_attrs;
      pprint_non_term_rules;
      pprint_non_term_loc]);;

let pprint_format_decl_desc fmt f =
    match f.format_decl with
    | Format_decl_non_term x -> pprint_non_term_defn fmt x

let pprint_format_decl =
    print_string "format_decl: "
    ++ (braces (concat ~sep:comma
    [pprint_format_decl_desc; pprint_format_decl_loc]));;

let pprint_format_decls_list fmt f =
    pf fmt "format_decls_list: ";
    brackets (list ~sep:comma pprint_format_decl) fmt f.format_decls

let pprint_decl_format = braces (concat ~sep:comma [pprint_format_name; pprint_format_decls_list; pprint_format_loc]);;

let pprint_top_decl fmt = function
    | Decl_use x -> pf fmt "decl use"
    | Decl_type y -> pf fmt "decl type"
    | Decl_fun z -> pf fmt "decl fun"
    | Decl_format a -> pf fmt " decl_format: " ; pprint_decl_format fmt a
    | Decl_nterm x -> pf fmt "placeholder ntermdecl printer";;

let print_ast fmt ast =
    pf fmt " ast: ";
    (brackets (list pprint_top_decl)) fmt ast.decls;;
