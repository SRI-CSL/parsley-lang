type ident   = string Location.loc
type literal = string Location.loc

type type_expr_desc =
  | TE_id of ident
  | TE_tuple  of type_expr list
  | TE_list of type_expr
  | TE_constr of ident * (type_expr list)

 and type_expr =
   { type_expr: type_expr_desc;
     type_expr_loc: Location.t }

type param_decl =
    (ident * type_expr) Location.loc

type binop =
  | Lt | Gt | Lteq | Gteq
  | Plus | Minus | Mult | Div
  | Match | Cons

type unop =
  | Uminus

type path = ident list

type expr_desc =
  | E_path of path
  | E_int of int
  | E_tuple of expr list
  | E_apply of expr * expr list
  | E_unop of unop * expr
  | E_binop of binop * expr * expr
  | E_index of expr * expr
  | E_literal of literal

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
  | RE_non_term of ident * ident option
  | RE_named_regex of rule_elem * ident (* regex of char-classes *)
  | RE_constraint of rule_constraint
  | RE_action of rule_action
  | RE_choice of rule_elem * rule_elem
  | RE_seq of rule_elem list
  | RE_star of rule_elem
  | RE_plus of rule_elem
  | RE_opt of rule_elem
  | RE_repeat of rule_elem * int
  | RE_char_class of char_class

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
      non_term_attrs: param_decl list;
      non_term_rules: rule list;
      non_term_loc: Location.t }

type use =
    { use_module: ident;
      use_idents: ident list;
      use_loc: Location.t }

type decl_desc =
  | Decl_non_term of non_term_defn
  | Decl_use of use
  | Decl_type of ident * type_expr

type decl =
    { decl: decl_desc;
      decl_loc: Location.t }

type format =
    { format_name: ident;
      format_param_decls: param_decl list;
      format_decls: decl list;
      format_loc: Location.t }
