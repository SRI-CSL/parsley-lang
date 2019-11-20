type tvar    = string Location.loc
type ident   = string Location.loc
type literal = string Location.loc
type path = ident list

type type_expr_desc =
  | TE_tvar of tvar
  | TE_tuple  of type_expr list
  | TE_list of type_expr
  | TE_constr of path * type_expr list
  | TE_typeof of path

 and type_expr =
   { type_expr: type_expr_desc;
     type_expr_loc: Location.t }

type type_rep_desc =
  | TR_expr of type_expr
  | TR_variant of (ident * type_expr list) list

 and type_rep =
   { type_rep: type_rep_desc;
     type_rep_loc: Location.t }

type param_decl =
    (ident * type_expr) Location.loc

type binop =
  | Lt | Gt | Lteq | Gteq | Eq
  | Plus | Minus | Mult | Div | Land | Lor
  | Cons

type unop =
  | Uminus | Not

type pattern_desc =
  | P_wildcard
  | P_var of ident
  | P_literal of literal
  | P_tuple of pattern list
  | P_variant of ident * pattern list

 and pattern =
   { pattern: pattern_desc;
     pattern_loc: Location.t }

type expr_desc =
  | E_path of path
  | E_int of int
  | E_constr of ident * expr list
  | E_tuple of expr list
  | E_apply of expr * expr list
  | E_unop of unop * expr
  | E_binop of binop * expr * expr
  | E_index of expr * expr
  | E_literal of literal
  | E_cast of expr * path
  | E_field of expr * path
  | E_case of expr * (pattern * expr) list
  | E_let of pattern * expr * expr
  | E_match of expr * path

 and expr =
   { expr: expr_desc;
     expr_loc: Location.t }

type stmt_desc =
  | S_assign of expr * expr

 and stmt =
   { stmt: stmt_desc;
     stmt_loc: Location.t }

type rule_action =
    { action_stmts: stmt list;
      action_loc: Location.t }

(* for now, use the same expression sublanguage in actions and constraints. *)
type rule_constraint =
    expr

type char_class_desc =
  | CC_named of ident
  | CC_wildcard
  | CC_literal of literal
  | CC_add of char_class * literal
  | CC_sub of char_class * literal

 and char_class =
   { char_class: char_class_desc;
     char_class_loc: Location.t }

type rule_elem_desc =
  | RE_literal of literal
  | RE_non_term of ident * ident option * (ident * expr) list option
  | RE_named_regex of rule_elem * ident (* regex of char-classes *)
  | RE_constraint of rule_constraint
  | RE_action of rule_action
  | RE_choice of rule_elem * rule_elem
  | RE_seq of rule_elem list
  | RE_star of rule_elem
  | RE_plus of rule_elem
  | RE_opt of rule_elem
  | RE_cclass_repeat of char_class * expr
  | RE_nterm_repeat of
      ident * (ident * expr) list option (* inh attrs *) * expr (* repeat *)
  | RE_char_class of char_class
  | RE_epsilon

 and rule_elem =
   { rule_elem: rule_elem_desc;
     rule_elem_loc: Location.t }

type rule =
    { rule_rhs: rule_elem list;
      rule_temps: param_decl list;
      rule_loc: Location.t }

type non_term_defn =
    { non_term_name: ident;
      non_term_varname: ident option;
      non_term_inh_attrs: param_decl list; (* inherited *)
      non_term_syn_attrs: param_decl list; (* synthesized *)
      non_term_rules: rule list;
      non_term_loc: Location.t }

type use =
    { use_module: ident;
      use_idents: ident list;
      use_loc: Location.t }

type type_defn =
    { type_defn_ident: ident;
      type_defn_tvars: tvar list;
      type_defn_body: type_rep;
      type_defn_loc: Location.t }

type fun_defn =
    { fun_defn_ident: ident;
      fun_defn_params: param_decl list;
      fun_defn_res_type: type_expr;
      fun_defn_body: expr;
      fun_defn_loc: Location.t }

type nterm_decl =
    { nterms: ident list;
      nterms_loc: Location.t }

type format_decl_desc =
  | Format_decl_non_term of non_term_defn

type format_decl =
    { format_decl: format_decl_desc;
      format_decl_loc: Location.t }

type format =
    { format_name: ident;
      format_decls: format_decl list;
      format_loc: Location.t }

type top_decl =
  | Decl_use of use
  | Decl_type of type_defn
  | Decl_fun of fun_defn
  | Decl_nterm of nterm_decl
  | Decl_format of format

type top_level =
    { decls: top_decl list }
