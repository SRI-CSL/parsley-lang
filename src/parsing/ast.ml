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

type tvar     = string Location.loc
type ident    = string Location.loc
type modident = string Location.loc
type literal  = string Location.loc
type bitint   = int    Location.loc
type 'b var   = (string * 'b) Location.loc

type bv_literal = bool list

(* names stripped of location, used in the type checker *)
type tname = TName of string
type dname = DName of string (* data constructor names *)
type lname = LName of string (* record field labels *)
type nname = NName of string (* non-terminal names *)
type mname = MName of string (* module name *)

type kind =
  | KStar
  | KNat
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
  | TR_bitfield of (ident * (bitint * bitint)) list
  | TR_defn of type_expr

and type_rep =
  {type_rep: type_rep_desc;
   type_rep_loc: Location.t}

type binop =
  | Lt | Gt | Lteq | Gteq | Eq | Neq
  | Plus | Minus | Mult | Mod | Div | Land | Lor
  | Or_b | And_b
  | Plus_s | At
  | Cons | Index

type unop =
  | Uminus | Not | Neg_b

type primitive_literal =
  | PL_int of int
  | PL_bytes of string
  | PL_unit
  | PL_bool of bool
  | PL_bit of bool
  | PL_bitvector of bv_literal

type ('a, 'b) pattern_desc =
  | P_wildcard
  | P_var of 'b var
  | P_literal of primitive_literal
  | P_variant of (ident * ident) * ('a, 'b) pattern list

and ('a, 'b) pattern =
  {pattern: ('a, 'b) pattern_desc;
   pattern_loc: Location.t;
   pattern_aux: 'a}

type ('a, 'b) expr_desc =
  | E_var of 'b var
  | E_constr of (ident * ident) * ('a, 'b) expr list
  | E_record of (ident * ('a, 'b) expr) list
  | E_apply of ('a, 'b) expr * ('a, 'b) expr list
  | E_unop of unop * ('a, 'b) expr
  | E_binop of binop * ('a, 'b) expr * ('a, 'b) expr
  | E_recop of ident * ident * ('a, 'b) expr
  | E_bitrange of ('a, 'b) expr * int * int
  | E_match of ('a, 'b) expr * (ident * ident)
  | E_literal of primitive_literal
  | E_field of ('a, 'b) expr * ident
  | E_mod_member of modident * ident
  | E_case of ('a, 'b) expr * (('a, 'b) pattern * ('a, 'b) expr) list
  | E_let of ('a, 'b) pattern * ('a, 'b) expr * ('a, 'b) expr
  | E_cast of ('a, 'b) expr * type_expr

and ('a, 'b) expr =
  {expr: ('a, 'b) expr_desc;
   expr_loc: Location.t;
   expr_aux: 'a}

type ('a, 'b) stmt_desc =
  | S_assign of ('a, 'b) expr * ('a, 'b) expr
  | S_let of ('a, 'b) pattern * ('a, 'b) expr * ('a, 'b) stmt list
  | S_case of ('a, 'b) expr * (('a, 'b) pattern * ('a, 'b) stmt list) list

and ('a, 'b) stmt =
  {stmt: ('a, 'b) stmt_desc;
   stmt_loc: Location.t}

type ('a, 'b) rule_action =
  {action_stmts: ('a, 'b) stmt list * ('a, 'b) expr option;
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

type ('a, 'b) regexp_desc =
  | RX_empty  (* for internal use *)
  | RX_literals of literal_set
  | RX_wildcard
  | RX_type of ident
  | RX_star of ('a, 'b) regexp * ('a, 'b) expr option
  | RX_opt of ('a, 'b) regexp
  | RX_choice of ('a, 'b) regexp list
  | RX_seq of ('a, 'b) regexp list

and ('a, 'b) regexp =
  {regexp: ('a, 'b) regexp_desc;
   regexp_loc: Location.t;
   regexp_aux: 'a}

type assign =
  | A_eq
  | A_in

type ('a, 'b) non_term_instance =
  ident * (ident * assign * ('a, 'b) expr) list option

type ('a, 'b) rule_elem_desc =
  (* bit-level support *)
  | RE_bitvector of bitint
  | RE_align of bitint
  | RE_pad of bitint * bv_literal
  | RE_bitfield of ident

  (* other basic primitives *)
  | RE_regexp of ('a, 'b) regexp
  | RE_non_term of ('a, 'b) non_term_instance

  (* binding for return values *)
  | RE_named of 'b var * ('a, 'b) rule_elem

  (* side-effects *)
  | RE_action of ('a, 'b) rule_action

  (* control flow and combinators *)
  | RE_constraint of ('a, 'b) expr
  | RE_seq of ('a, 'b) rule_elem list
  | RE_choice of ('a, 'b) rule_elem list
  | RE_star of ('a, 'b) rule_elem * ('a, 'b) expr option
  | RE_opt of ('a, 'b) rule_elem
  | RE_epsilon

  (* view control *)
  | RE_set_view of ('a, 'b) expr
  | RE_at_pos of ('a, 'b) expr * ('a, 'b) rule_elem
  | RE_at_view of ('a, 'b) expr * ('a, 'b) rule_elem
  | RE_map_views of ('a, 'b) expr * ('a, 'b) rule_elem

  (* internal use only: to flatten regexps after typing *)
  | RE_seq_flat  of ('a, 'b) rule_elem list

and ('a, 'b) rule_elem =
  {rule_elem: ('a, 'b) rule_elem_desc;
   rule_elem_loc: Location.t;
   rule_elem_aux: 'a}

type ('a, 'b) rule =
  {rule_rhs: ('a, 'b) rule_elem list;
   rule_temps: ('b var * type_expr * ('a, 'b) expr) list;
   rule_loc: Location.t}

type ('a, 'b) attr_list_type =
  | ALT_type of ident
  | ALT_decls of (ident * type_expr * 'a * ('a, 'b) expr option) list

type ('a, 'b) non_term_defn =
  {non_term_name: ident;
   non_term_varname: 'b var option;
   non_term_inh_attrs: ('b var * type_expr * 'a) list; (* inherited *)
   non_term_syn_attrs: ('a, 'b) attr_list_type; (* synthesized *)
   non_term_rules: ('a, 'b) rule list;
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

type ('a, 'b) fun_defn =
  {fun_defn_ident: 'b var;
   fun_defn_tvars: tvar list;
   fun_defn_params: ('b var * type_expr * 'a) list;
   fun_defn_res_type: type_expr;
   fun_defn_body: ('a, 'b) expr;
   fun_defn_recursive: bool;
   fun_defn_synth: bool;  (* whether this was synthesized *)
   fun_defn_loc: Location.t;
   fun_defn_aux: 'a}

type ('a, 'b) rec_funs_defn =
  {recfuns: ('a, 'b) fun_defn list; (* mutually recursive *)
   recfuns_loc: Location.t}

type ('a, 'b) const_defn =
  {const_defn_ident: 'b var;
   const_defn_type: type_expr;
   const_defn_val: ('a, 'b) expr;
   const_defn_loc: Location.t;
   const_defn_aux: 'a}

type deco_arg =
  | Deco_key of ident
  | Deco_keyvalue of ident * ident

type decorator =
  {deco_type: ident;
   deco_value: ident;
   deco_args: deco_arg list;
   deco_loc: Location.t}

type ('a, 'b) format_decl =
  {format_decl: ('a, 'b) non_term_defn;
   format_deco: decorator list option;
   format_decl_loc: Location.t}

type ('a, 'b) format =
  {format_decls: ('a, 'b) format_decl list;
   format_loc: Location.t}

type ('a, 'b) pre_decl =
  | PDecl_use of use
  | PDecl_types of type_decl list * Location.t (* possibly mutually recursive *)
  | PDecl_const of ('a, 'b) const_defn
  | PDecl_fun of ('a, 'b) fun_defn
  | PDecl_recfuns of ('a, 'b) rec_funs_defn
  | PDecl_format of ('a, 'b) format

type ('a, 'b) pre_top_level =
  {pre_decls: ('a, 'b) pre_decl list}

(* flattened version after including use files *)
type ('a, 'b) top_decl =
  | Decl_types of type_decl list * Location.t (* possibly mutually recursive *)
  | Decl_const of ('a, 'b) const_defn
  | Decl_fun of ('a, 'b) fun_defn
  | Decl_recfuns of ('a, 'b) rec_funs_defn
  | Decl_format of ('a, 'b) format

type ('a, 'b) program =
  {decls: ('a, 'b) top_decl list}

let var_name v =
  fst (Location.value v)

(* max concrete bit-width in spec.
   we need at least a width of 1 due to the std library.
 *)
let max_width : int ref = ref 1
let register_bitwidth i =
  max_width := max !max_width i
