type tvar     = string Location.loc
type ident    = string Location.loc
type modident = string Location.loc
type literal  = string Location.loc

(* names stripped of location, used in the type checker *)
type tname = MultiEquation.tname
type dname = DName of string (* data constructor names *)
type lname = LName of string (* record field labels *)
type nname = NName of string (* non-terminal names *)
type mname = MName of string (* module name *)

type kind =
  | KStar
  | KArrow of kind * kind

type type_expr_desc =
  | TE_tvar of tvar
  | TE_tapp of type_expr * type_expr list

and type_expr =
  {type_expr: type_expr_desc;
   type_expr_loc: Location.t}

type type_rep_desc =
  | TR_variant of (ident * type_expr option) list
  | TR_record of (ident * type_expr) list
  | TR_defn of type_expr

and type_rep =
  {type_rep: type_rep_desc;
   type_rep_loc: Location.t}

type binop =
  | Lt | Gt | Lteq | Gteq | Eq | Neq
  | Plus | Minus | Mult | Div | Land | Lor
  | Plus_s | At
  | Cons | Index

type unop =
  | Uminus | Not

type primitive_literal =
  | PL_int of int
  | PL_string of string
  | PL_unit
  | PL_bool of bool

type 'a pattern_desc =
  | P_wildcard
  | P_var of ident
  | P_literal of primitive_literal
  | P_variant of (ident * ident) * 'a pattern list

and 'a pattern =
  {pattern: 'a pattern_desc;
   pattern_loc: Location.t;
   pattern_aux: 'a}

type 'a expr_desc =
  | E_var of ident
  | E_constr of (ident * ident) * 'a expr list
  | E_record of (ident * 'a expr) list
  | E_apply of 'a expr * 'a expr list
  | E_unop of unop * 'a expr
  | E_binop of binop * 'a expr * 'a expr
  | E_match of 'a expr * (ident * ident)
  | E_literal of primitive_literal
  | E_field of 'a expr * ident
  | E_mod_member of modident * ident
  | E_case of 'a expr * ('a pattern * 'a expr) list
  | E_let of 'a pattern * 'a expr * 'a expr
  | E_cast of 'a expr * type_expr

and 'a expr =
  {expr: 'a expr_desc;
   expr_loc: Location.t;
   expr_aux: 'a}

type 'a stmt_desc =
  | S_assign of 'a expr * 'a expr
  | S_let of 'a pattern * 'a expr * 'a stmt list
  | S_case of 'a expr * ('a pattern * 'a stmt list) list

and 'a stmt =
  {stmt: 'a stmt_desc;
   stmt_loc: Location.t}

type 'a rule_action =
  {action_stmts: 'a stmt list * 'a expr option;
   action_loc: Location.t}

(* for now, use the same expression sublanguage in actions and constraints. *)

type literal_set_desc =
  | LS_type of ident
  | LS_set of literal list
  | LS_diff of literal_set * literal_set
  | LS_range of literal * literal

and literal_set =
  {literal_set: literal_set_desc;
   literal_set_loc: Location.t}

type 'a regexp_desc =
  | RX_literals of literal_set
  | RX_wildcard
  | RX_type of ident
  | RX_star of 'a regexp * 'a expr option
  | RX_opt of 'a regexp
  | RX_choice of 'a regexp list
  | RX_seq of 'a regexp list

and 'a regexp =
  {regexp: 'a regexp_desc;
   regexp_loc: Location.t;
   regexp_aux: 'a}

type 'a rule_elem_desc =
  | RE_regexp of 'a regexp
  | RE_non_term of ident * (ident * 'a expr) list option
  | RE_constraint of 'a expr
  | RE_action of 'a rule_action
  | RE_named of ident * 'a rule_elem
  | RE_seq of 'a rule_elem list
  | RE_choice of 'a rule_elem list
  | RE_star of 'a rule_elem * 'a expr option
  | RE_opt of 'a rule_elem
  | RE_epsilon
  | RE_at_pos of 'a expr * 'a rule_elem
  | RE_at_buf of 'a expr * 'a rule_elem
  | RE_map_bufs of 'a expr * 'a rule_elem

and 'a rule_elem =
  {rule_elem: 'a rule_elem_desc;
   rule_elem_loc: Location.t;
   rule_elem_aux: 'a}

type 'a rule =
  {rule_rhs: 'a rule_elem list;
   rule_temps: (ident * type_expr * 'a expr) list;
   rule_loc: Location.t}

type 'a attr_list_type =
  | ALT_type of ident
  | ALT_decls of (ident * type_expr * 'a expr option) list

type 'a non_term_defn =
  {non_term_name: ident;
   non_term_varname: ident option;
   non_term_inh_attrs: (ident * type_expr) list; (* inherited *)
   non_term_syn_attrs: 'a attr_list_type; (* synthesized *)
   non_term_rules: 'a rule list;
   non_term_loc: Location.t}

type use =
  {use_modules: ident list;
   use_loc: Location.t}

type type_decl =
  {type_decl_ident: ident;
   type_decl_kind: kind;
   type_decl_tvars: tvar list;
   type_decl_body: type_rep;
   type_decl_loc: Location.t}

type 'a fun_defn =
  {fun_defn_ident: ident;
   fun_defn_tvars: tvar list;
   fun_defn_params: (ident * type_expr) list;
   fun_defn_res_type: type_expr;
   fun_defn_body: 'a expr;
   fun_defn_recursive: bool;
   fun_defn_loc: Location.t;
   fun_defn_aux: 'a}

type attribute_arg =
  | Attr_key of ident
  | Attr_keyvalue of ident * ident

type attribute =
  {attr_type: ident;
   attr_value: ident;
   attr_args: attribute_arg list;
   attr_loc: Location.t}

type 'a format_decl =
  {format_decl: 'a non_term_defn;
   format_attr: attribute option;
   format_decl_loc: Location.t}

type 'a format =
  {format_decls: 'a format_decl list;
   format_loc: Location.t}

type 'a pre_decl =
  | PDecl_use of use
  | PDecl_types of type_decl list * Location.t (* possibly mutually recursive *)
  | PDecl_fun of 'a fun_defn
  | PDecl_format of 'a format

type 'a pre_top_level =
  {pre_decls: 'a pre_decl list}

(* flattened version after including use files *)
type 'a top_decl =
  | Decl_types of type_decl list * Location.t (* possibly mutually recursive *)
  | Decl_fun of 'a fun_defn
  | Decl_format of 'a format

type 'a program =
  {decls: 'a top_decl list}
