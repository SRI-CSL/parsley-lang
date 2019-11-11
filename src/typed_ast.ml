(* The ast after type-checking.
 *
 * It has the same structure as that in the ast module, except that
 * type and program variables have unique identifiers, and top-level
 * expressions are annotated with their types.
 *)

module TU = Typing_utils

type kind = K_type

type var = Var

type type_expr_desc =
  | TE_tvar of kind TU.Tvar.t
  | TE_tuple of type_expr list
  | TE_list of type_expr
  | TE_constr of Ast.path * (type_expr list)
  | TE_app of Ast.path * type_expr list

 and type_expr =
   { type_expr: type_expr_desc;
     type_expr_loc: Location.t }

type type_rep_desc =
  | TR_expr of type_expr
  | TR_variant of (Ast.ident * type_expr list) list

 and type_rep =
   { type_rep: type_rep_desc;
     type_rep_loc: Location.t }

type param_decl =
    (Ast.ident * type_expr) Location.loc

type pattern_desc =
  | P_wildcard
  | P_var of var TU.Tvar.t
  | P_literal of Ast.literal
  | P_tuple of pattern list
  | P_variant of Ast.ident * pattern list

 and pattern =
   { pattern: pattern_desc;
     pattern_loc: Location.t }

type expr_desc =
  | E_path of Ast.path
  | E_int of int
  | E_constr of Ast.ident * expr list
  | E_tuple of expr list
  | E_apply of expr * expr list
  | E_unop of Ast.unop * expr
  | E_binop of Ast.binop * expr * expr
  | E_index of expr * expr
  | E_literal of Ast.literal
  | E_cast of expr * Ast.path
  | E_field of expr * Ast.path
  | E_case of expr * (pattern * expr) list
  | E_let of pattern * expr * expr

 and expr =
   { expr: expr_desc;
     expr_type: type_expr_desc;  (* computed by type-checker *)
     expr_loc: Location.t }

type stmt_desc =
  | S_assign of expr * expr

 and stmt =
   { stmt: stmt_desc;
     stmt_loc: Location.t }

type rule_action =
    { action_stmts: stmt list;
      action_loc: Location.t }

type rule_constraint =
    expr

type char_class_desc =
  | CC_named of Ast.ident
  | CC_wildcard
  | CC_literal of Ast.literal
  | CC_add of char_class * Ast.literal
  | CC_sub of char_class * Ast.literal

 and char_class =
   { char_class: char_class_desc;
     char_class_loc: Location.t }

type rule_elem_desc =
  | RE_literal of Ast.literal
  | RE_non_term of Ast.ident * Ast.ident option * (Ast.ident * expr) list option
  | RE_named_regex of rule_elem * Ast.ident (* regex of char-classes *)
  | RE_constraint of rule_constraint
  | RE_action of rule_action
  | RE_choice of rule_elem * rule_elem
  | RE_seq of rule_elem list
  | RE_star of rule_elem
  | RE_plus of rule_elem
  | RE_opt of rule_elem
  | RE_repeat of char_class * int
  | RE_char_class of char_class

 and rule_elem =
   { rule_elem: rule_elem_desc;
     rule_elem_loc: Location.t }

type rule =
    { rule_rhs: rule_elem list;
      rule_temps: param_decl list;
      rule_loc: Location.t }

type non_term_defn =
    { non_term_name: Ast.ident;
      non_term_varname: Ast.ident option;
      non_term_inh_attrs: param_decl list; (* inherited *)
      non_term_syn_attrs: param_decl list; (* synthesized *)
      non_term_rules: rule list;
      non_term_loc: Location.t }

type use =
    { use_module: Ast.ident;
      use_idents: Ast.ident list;
      use_loc: Location.t }

type type_defn =
    { type_defn_ident: Ast.ident;
      type_defn_tvars: kind TU.Tvar.t list;
      type_defn_body: type_rep;
      type_defn_loc: Location.t }

type fun_defn =
    { fun_defn_ident: Ast.ident;
      fun_defn_tvars: kind TU.Tvar.t list; (* universal tvars *)
      fun_defn_params: param_decl list;
      fun_defn_res_type: type_expr;
      fun_defn_body: expr;
      fun_defn_loc: Location.t }

type format_decl_desc =
  | Format_decl_non_term of non_term_defn

type format_decl =
    { format_decl: format_decl_desc;
      format_decl_loc: Location.t }

type format =
    { format_name: Ast.ident;
      format_decls: format_decl list;
      format_loc: Location.t }

type top_decl =
  | Decl_use of use
  | Decl_type of type_defn
  | Decl_fun of fun_defn
  | Decl_format of format

type top_level =
    { decls: top_decl list }
