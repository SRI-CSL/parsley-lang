type tvar    = string Location.loc
type ident   = string Location.loc
type literal = string Location.loc
type path    = ident list

(* names stripped of location, used in the type checker *)
type tname = MultiEquation.tname
type dname = DName of string (* data constructor names *)
type lname = LName of string (* record field labels *)

type kind =
  | KStar
  | KArrow of kind * kind

type type_expr_desc =
  | TE_tvar of tvar
  | TE_tapp of type_expr * type_expr list
  | TE_record of param_decl list

and param_decl =
  (ident * type_expr) Location.loc

and type_expr =
  { type_expr: type_expr_desc;
    type_expr_loc: Location.t }

type type_rep_desc =
  (* The type signature in 'type_expr' includes the return type for the
   * variant constructor 'ident'; i.e. it is a full function signature. *)
  | TR_algebraic of (ident * type_expr) list
  | TR_defn of type_expr

and type_rep =
  { type_rep: type_rep_desc;
    type_rep_loc: Location.t }

type binop =
  | Lt | Gt | Lteq | Gteq | Eq | Neq
  | Plus | Minus | Mult | Div | Land | Lor
  | Cons | Index

type unop =
  | Uminus | Not

type primitive_literal =
  | PL_int of int
  | PL_string of string

type pattern_desc =
  | P_wildcard
  | P_var of ident
  | P_literal of primitive_literal
  | P_tuple of pattern list
  | P_variant of (ident * ident) * pattern list

and pattern =
  { pattern: pattern_desc;
    pattern_loc: Location.t }

type expr_desc =
  | E_path of path
  | E_constr of ident * ident * expr list
  | E_record of (ident * expr) list
  | E_apply of expr * expr list
  | E_unop of unop * expr
  | E_binop of binop * expr * expr
  | E_match of expr * path * ident
  | E_literal of primitive_literal
  | E_field of expr * ident
  | E_list of expr list
  | E_case of expr * (pattern * expr) list
  | E_let of pattern * expr * expr
  | E_cast of expr * type_expr

and expr =
  { expr: expr_desc;
    expr_loc: Location.t }

type stmt_desc =
  | S_expr of expr
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

type literal_set_desc =
  | LS_type of ident
  | LS_set of literal list
  | LS_diff of literal_set * literal_set
  | LS_range of literal * literal

and literal_set =
  { literal_set: literal_set_desc;
    literal_set_loc: Location.t }

type regexp_desc =
  | RX_literals of literal_set
  | RX_wildcard
  | RX_type of ident
  | RX_star of regexp * expr option
  | RX_opt of regexp
  | RX_choice of regexp list
  | RX_seq of regexp list

and regexp =
  { regexp: regexp_desc;
    regexp_loc: Location.t }

type rule_elem_desc =
  | RE_regexp of regexp
  | RE_non_term of ident * (ident * expr) list option
  | RE_constraint of rule_constraint
  | RE_action of rule_action
  | RE_named of ident * rule_elem
  | RE_seq of rule_elem list
  | RE_choice of rule_elem list
  | RE_star of rule_elem * expr option
  | RE_opt of rule_elem
  | RE_epsilon
  | RE_at_pos of expr * rule_elem
  | RE_at_buf of expr * rule_elem
  | RE_map_bufs of expr * rule_elem

and rule_elem =
  { rule_elem: rule_elem_desc;
    rule_elem_loc: Location.t }

type rule =
  { rule_rhs: rule_elem list;
    rule_temps: param_decl list;
    rule_loc: Location.t }

type attr_list_type =
  | ALT_type of ident  (* TODO: support record instantiation? *)
  | ALT_decls of param_decl list

type non_term_defn =
  { non_term_name: ident;
    non_term_varname: ident option;
    non_term_inh_attrs: attr_list_type; (* inherited *)
    non_term_syn_attrs: attr_list_type; (* synthesized *)
    non_term_rules: rule list;
    non_term_loc: Location.t }

type use =
  { use_modules: ident list;
    use_loc: Location.t }

type type_decl =
  { type_decl_ident: ident;
    type_decl_kind: kind;
    type_decl_tvars: tvar list;
    type_decl_body: type_rep;
    type_decl_loc: Location.t }

type fun_defn =
  { fun_defn_ident: ident;
    fun_defn_params: param_decl list;
    fun_defn_res_type: type_expr;
    fun_defn_body: expr;
    fun_defn_loc: Location.t }

type nterm_decl =
  { nterms: ident list;
    nterms_loc: Location.t }

type attribute_arg =
  | Attr_key of ident
  | Attr_keyvalue of ident * ident

type attribute =
  { attr_type: ident;
    attr_value: ident;
    attr_args: attribute_arg list;
    attr_loc: Location.t }

type format_decl_desc =
  | Format_decl_non_term of non_term_defn

type format_decl =
  { format_decl: format_decl_desc;
    format_attr: attribute option;
    format_decl_loc: Location.t }

type format =
  { format_decls: format_decl list;
    format_loc: Location.t }

type top_decl =
  | Decl_use of use
  | Decl_types of type_decl list (* possibly mutually recursive *)
  | Decl_fun of fun_defn
  | Decl_nterm of nterm_decl
  | Decl_format of format

type top_level =
  { decls: top_decl list }

(* flattened version after including use files *)
type flat_top_decl =
  | Flat_decl_types of type_decl list (* possibly mutually recursive *)
  | Flat_decl_fun of fun_defn
  | Flat_decl_nterm of nterm_decl
  | Flat_decl_format of format

type flat_top_level =
  { flat_decls: flat_top_decl list }
