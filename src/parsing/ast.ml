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
type tname = TName of string (* types *)
type dname = DName of string (* data constructors *)
type lname = LName of string (* record field labels *)
type nname = NName of string (* non-terminals *)
type vname = VName of string (* values (functions, constants) *)

(* module qualifiers*)

type 'm modul =
  | Modul of 'm

type raw_mod =
  modident option

type mod_qual =
  | Mod_explicit of modident
  | Mod_stdlib
  | Mod_inferred of string

(* module qualified identifiers *)
type mname = mod_qual modul
type full_tname = mname * tname
type full_dname = mname * dname
type full_lname = mname * lname
type full_nname = mname * nname
type full_vname = mname * vname

type kind =
  | KStar
  | KNat
  | KArrow of kind * kind

type num_width =
  | NW_size
  | NW_8
  | NW_16
  | NW_32
  | NW_64

let str_of_num_width = function
  | NW_size -> "size"
  | NW_8    -> "8"
  | NW_16   -> "16"
  | NW_32   -> "32"
  | NW_64   -> "64"

type signed = S_signed | S_unsigned

let str_of_signed = function
  | S_signed   -> "i"
  | S_unsigned -> "u"

type num_t = signed * num_width

let str_of_num_t (s, w) =
  str_of_signed s ^ str_of_num_width w

(* utility defines *)

let i8_t    = S_signed, NW_8
let i16_t   = S_signed, NW_16
let i32_t   = S_signed, NW_32
let i64_t   = S_signed, NW_64
let isize_t = S_signed, NW_size

let u8_t    = S_unsigned, NW_8
let u16_t   = S_unsigned, NW_16
let u32_t   = S_unsigned, NW_32
let u64_t   = S_unsigned, NW_64
let usize_t = S_unsigned, NW_size

type 'm gen_type_expr_desc =
  | TE_tvar  of tvar                     (* can only appear in leaf position *)
  | TE_tname of 'm modul * ident         (* can appear in leaf and constructor position *)
  | TE_tapp  of 'm gen_type_expr * 'm gen_type_expr list

and 'm gen_type_expr =
  {type_expr:     'm gen_type_expr_desc;
   type_expr_loc: Location.t}

type 'm gen_type_rep_desc =
  | TR_variant  of (ident * 'm gen_type_expr option) list
  | TR_record   of (ident * 'm gen_type_expr) list
  | TR_bitfield of (ident * (bitint * bitint)) list
  | TR_defn     of 'm gen_type_expr

and 'm gen_type_rep =
  {type_rep:     'm gen_type_rep_desc;
   type_rep_loc: Location.t}

type binop =
  | Lt of num_t   | Gt of num_t    | Lteq of num_t | Gteq of num_t
  | Plus of num_t | Minus of num_t | Mult of num_t | Div of num_t | Mod of num_t
  | Lshft of num_t | Rshft of num_t | Ashft of num_t
  | Iand of num_t | Ior of num_t | Ixor of num_t
  | Eq | Neq
  | Land | Lor
  | Or_b | And_b
  | Plus_s | At
  | Cons | Index

type unop =
  | Uminus of num_t | Inot of num_t | Not | Neg_b

type primitive_literal =
  | PL_unit
  | PL_int       of int * num_t
  | PL_bytes     of string
  | PL_bool      of bool
  | PL_bit       of bool
  | PL_bitvector of bv_literal

type ('a, 'b, 'm) pattern_desc =
  | P_wildcard
  | P_var     of 'b var
  | P_literal of primitive_literal
  | P_variant of ('m modul * ident * ident) * ('a, 'b, 'm) pattern list

and ('a, 'b, 'm) pattern =
  {pattern:     ('a, 'b, 'm) pattern_desc;
   pattern_loc: Location.t;
   pattern_aux: 'a}

type ('a, 'b, 'm) expr_desc =
  | E_var        of 'b var
  | E_constr     of ('m modul * ident * ident) * ('a, 'b, 'm) expr list
  | E_record     of (('m modul * ident) * ('a, 'b, 'm) expr) list
  | E_apply      of ('a, 'b, 'm) expr * ('a, 'b, 'm) expr list
  | E_unop       of unop * ('a, 'b, 'm) expr
  | E_binop      of binop * ('a, 'b, 'm) expr * ('a, 'b, 'm) expr
  | E_recop      of ('m modul * ident * ident) * ('a, 'b, 'm) expr
  | E_bitrange   of ('a, 'b, 'm) expr * int * int
  | E_match      of ('a, 'b, 'm) expr * ('m modul * ident * ident)
  | E_literal    of primitive_literal
  | E_field      of ('a, 'b, 'm) expr * ('m modul * ident)
  | E_mod_member of modident * ident
  | E_case       of ('a, 'b, 'm) expr * (('a, 'b, 'm) pattern * ('a, 'b, 'm) expr) list
  | E_let        of ('a, 'b, 'm) pattern * ('a, 'b, 'm) expr * ('a, 'b, 'm) expr
  | E_cast       of ('a, 'b, 'm) expr * 'm gen_type_expr

and ('a, 'b, 'm) expr =
  {expr:     ('a, 'b, 'm) expr_desc;
   expr_loc: Location.t;
   expr_aux: 'a}

type ('a, 'b, 'm) stmt_desc =
  | S_assign of ('a, 'b, 'm) expr * ('a, 'b, 'm) expr
  | S_let    of ('a, 'b, 'm) pattern * ('a, 'b, 'm) expr * ('a, 'b, 'm) stmt list
  | S_case   of ('a, 'b, 'm) expr * (('a, 'b, 'm) pattern * ('a, 'b, 'm) stmt list) list
  | S_print  of bool (* data: true -> ascii | false -> hex *) * ('a, 'b, 'm) expr

and ('a, 'b, 'm) stmt =
  {stmt:     ('a, 'b, 'm) stmt_desc;
   stmt_loc: Location.t}

type ('a, 'b, 'm) rule_action =
  {action_stmts: ('a, 'b, 'm) stmt list * ('a, 'b, 'm) expr option;
   action_loc:   Location.t}

(* for now, use the same expression sublanguage in actions and constraints. *)

type 'm literal_set_desc =
  | LS_type  of 'm modul * ident
  | LS_set   of literal list
  | LS_diff  of 'm literal_set * 'm literal_set
  | LS_range of literal * literal

and 'm literal_set =
  {literal_set:     'm literal_set_desc;
   literal_set_loc: Location.t}

type ('a, 'b, 'm) regexp_desc =
  | RX_empty    (* for internal use *)
  | RX_wildcard
  | RX_literals of 'm literal_set
  | RX_type     of 'm modul * ident
  | RX_star     of ('a, 'b, 'm) regexp * ('a, 'b, 'm) expr option
  | RX_opt      of ('a, 'b, 'm) regexp
  | RX_choice   of ('a, 'b, 'm) regexp list
  | RX_seq      of ('a, 'b, 'm) regexp list

and ('a, 'b, 'm) regexp =
  {regexp:     ('a, 'b, 'm) regexp_desc;
   regexp_loc: Location.t;
   regexp_mod: string;
   regexp_aux: 'a}

type assign =
  | A_eq
  | A_in

type scan_direction =
  | Scan_forward
  | Scan_backward

type ('a, 'b, 'm) non_term_instance =
  'm modul * ident * (ident * assign * ('a, 'b, 'm) expr) list option

type ('a, 'b, 'm) rule_elem_desc =
  (* bit-level support *)
  | RE_bitvector of bitint
  | RE_align     of bitint
  | RE_pad       of bitint * bv_literal
  | RE_bitfield  of ident

  (* other basic primitives *)
  | RE_regexp   of ('a, 'b, 'm) regexp
  | RE_non_term of ('a, 'b, 'm) non_term_instance
  | RE_scan     of (literal * scan_direction)

  (* binding for return values *)
  | RE_named of 'b var * ('a, 'b, 'm) rule_elem

  (* side-effects *)
  | RE_action of ('a, 'b, 'm) rule_action

  (* control flow and combinators *)
  | RE_epsilon    (* nop *)
  | RE_constraint of ('a, 'b, 'm) expr
  | RE_seq        of ('a, 'b, 'm) rule_elem list
  | RE_choice     of ('a, 'b, 'm) rule_elem list
  | RE_star       of ('a, 'b, 'm) rule_elem * ('a, 'b, 'm) expr option
  | RE_opt        of ('a, 'b, 'm) rule_elem

  (* view control *)
  | RE_set_view  of ('a, 'b, 'm) expr
  | RE_at_pos    of ('a, 'b, 'm) expr * ('a, 'b, 'm) rule_elem
  | RE_at_view   of ('a, 'b, 'm) expr * ('a, 'b, 'm) rule_elem
  | RE_map_views of ('a, 'b, 'm) expr * ('a, 'b, 'm) rule_elem

  (* internal use only: to flatten regexps after typing *)
  | RE_seq_flat  of ('a, 'b, 'm) rule_elem list

and ('a, 'b, 'm) rule_elem =
  {rule_elem:     ('a, 'b, 'm) rule_elem_desc;
   rule_elem_mod: string;
   rule_elem_loc: Location.t;
   rule_elem_aux: 'a}

type ('a, 'b, 'm) rule =
  {rule_rhs:   ('a, 'b, 'm) rule_elem list;
   rule_temps: ('b var * 'm gen_type_expr * ('a, 'b, 'm) expr) list;
   rule_loc:   Location.t}

type ('a, 'b, 'm) attr_list_type =
  | ALT_type  of ident
  | ALT_decls of (ident * 'm gen_type_expr * 'a * ('a, 'b, 'm) expr option) list

type ('a, 'b, 'm) non_term_defn =
  {non_term_name:      ident;
   non_term_varname:   'b var option;
   non_term_inh_attrs: ('b var * 'm gen_type_expr * 'a) list; (* inherited *)
   non_term_syn_attrs: ('a, 'b, 'm) attr_list_type;         (* synthesized *)
   non_term_rules:     ('a, 'b, 'm) rule list;
   non_term_mod:       string;
   non_term_loc:       Location.t}

type 'm type_decl =
  {type_decl_ident: ident;
   type_decl_kind:  kind;
   type_decl_tvars: tvar list;
   type_decl_body:  'm gen_type_rep;
   type_decl_mod:   string;
   type_decl_loc:   Location.t}

type ('a, 'b, 'm) fun_defn =
  {fun_defn_ident:     'b var;
   fun_defn_tvars:     tvar list;
   fun_defn_params:    ('b var * 'm gen_type_expr * 'a) list;
   fun_defn_res_type:  'm gen_type_expr;
   fun_defn_body:      ('a, 'b, 'm) expr;
   fun_defn_recursive: bool;
   fun_defn_synth:     bool;  (* whether this was synthesized *)
   fun_defn_mod:       string;
   fun_defn_loc:       Location.t;
   fun_defn_aux:       'a}

type ('a, 'b, 'm) rec_funs_defn =
  {recfuns:     ('a, 'b, 'm) fun_defn list; (* mutually recursive *)
   recfuns_loc: Location.t}

type ('a, 'b, 'm) const_defn =
  {const_defn_ident: 'b var;
   const_defn_type:  'm gen_type_expr;
   const_defn_val:   ('a, 'b, 'm) expr;
   const_defn_mod:   string;
   const_defn_loc:   Location.t;
   const_defn_aux:   'a}

type deco_arg =
  | Deco_key      of ident
  | Deco_keyvalue of ident * ident

type decorator =
  {deco_type:  ident;
   deco_value: ident;
   deco_args:  deco_arg list;
   deco_loc:   Location.t}

type ('a, 'b, 'm) format_decl =
  {format_decl:     ('a, 'b, 'm) non_term_defn;
   format_deco:     decorator list option;
   format_decl_loc: Location.t}

type ('a, 'b, 'm) format =
  {format_decls: ('a, 'b, 'm) format_decl list;
   format_loc:   Location.t}

(* Pre-AST from parsing a single file. *)
type inc_list = ident list
type mod_list = modident list
type ('a, 'b) pre_decl =
  | PDecl_include of inc_list
  | PDecl_import  of mod_list
  | PDecl_types   of raw_mod type_decl list * Location.t
  | PDecl_const   of ('a, 'b, raw_mod) const_defn
  | PDecl_fun     of ('a, 'b, raw_mod) fun_defn
  | PDecl_recfuns of ('a, 'b, raw_mod) rec_funs_defn
  | PDecl_format  of ('a, 'b, raw_mod) format

type ('a, 'b) pre_spec_module =
  {pre_decls: ('a, 'b) pre_decl list}

(* Spec AST: flattened version after include files *)

type type_expr      = mod_qual gen_type_expr
type type_expr_desc = mod_qual gen_type_expr_desc

type ('a, 'b) top_decl =
  | Decl_types   of mod_qual type_decl list * Location.t
  | Decl_const   of ('a, 'b, mod_qual) const_defn
  | Decl_fun     of ('a, 'b, mod_qual) fun_defn
  | Decl_recfuns of ('a, 'b, mod_qual) rec_funs_defn
  | Decl_format  of ('a, 'b, mod_qual) format

type ('a, 'b) spec_module =
  {decls: ('a, 'b) top_decl list}

let var_name v =
  fst (Location.value v)

(* The maximum concrete bit-width in spec.
   We need at least a width of 64 due to the max int size in the std
   library. *)
let max_width : int ref = ref 64
let register_bitwidth i =
  max_width := max !max_width i

(* The module being currently parsed, which should always be set when
   this function is called. *)
let cur_module : string option ref = ref None
let set_cur_module m =
  cur_module := Some m
let get_cur_module () : string =
  match !cur_module with
    | None   -> assert false
    | Some m -> m
