/**************************************************************************/
/*  This program is free software; you can redistribute it and/or modify  */
/*  it under the terms of the GNU General Public License as published by  */
/*  the Free Software Foundation; version 2 of the License.               */
/*                                                                        */
/*  This program is distributed in the hope that it will be useful, but   */
/*  WITHOUT ANY WARRANTY; without even the implied warranty of            */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU     */
/*  General Public License for more details.                              */
/*                                                                        */
/*  You should have received a copy of the GNU General Public License     */
/*  along with this program; if not, write to the Free Software           */
/*  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA         */
/*  02110-1301 USA                                                        */
/*                                                                        */
/**************************************************************************/

%{
open Ast
open Parseerror
%}

%token EOF
%token FORMAT TYPE BITFIELD AND FUN RECFUN INCLUDE IMPORT OF CASE LET
%token IN CONST FOREIGN
%token PRINT PRINTT
%token DECO LSRCO RSRCO
%token EPSILON PAD ALIGN USE_BITFIELD
%token SLASH_SF_LBRACK SLASH_SB_LBRACK

%token LBRACE RBRACE LPAREN RPAREN LBRACK RBRACK LLBRACK RRBRACK LBRACKRBRACK
%token LPARBAR RPARBAR LANGLE RANGLE SYN_BEGIN SYN_END
%token SET_VIEW AT_POS AT_VIEW AT_MAP HASH
%token BAR COMMA COLON COLONEQ SEMICOLON SEMISEMI DOT QUESTION ARROW LARROW
%token CARET PLUS_S AT BAR_B AND_B TILDE
%token EQ NEQ LAND LOR
%token CONSTR_MATCH COLONCOLON BACKSLASH EXCLAIM UNDERSCORE DOTDOT
%token STAR POS NEG

%token<Ast.num_t> LT GT LTEQ GTEQ
%token<Ast.num_t> MUL PLUS MINUS MOD DIV
%token<Ast.num_t> LSHFT RSHFT ASHFT
%token<Ast.num_t> IB_NOT IB_AND IB_OR IB_XOR

%token<Ast.literal> LITERAL
%token<Ast.ident>   ID
%token<Ast.ident>   UID
%token<Ast.tvar>    TVAR

%token<(string * Ast.num_t) Location.loc> INT_LITERAL
%token<string Location.loc> BV_LITERAL RAW_INT

%token<string Location.loc option * string Location.loc * string Location.loc> CONSTR

%start<(unit, unit) Ast.pre_spec_module> toplevel

(* operators are increasing precedence order. *)
%nonassoc IN
%right EXCLAIM
%left  LAND LOR
%left  IB_AND IB_OR IB_XOR
%left  LT GT LTEQ GTEQ EQ NEQ CONSTR_MATCH
%left  BAR
%left  BACKSLASH
%right AT
%right COLONCOLON
%left  LSHFT RSHFT ASHFT
%left  PLUS MINUS PLUS_S POS NEG
%left  MUL MOD DIV QUESTION STAR
%left  BAR_B
%left  AND_B
%left  CARET
%nonassoc UMINUS
%left  LPAREN LBRACK LLBRACK
%left  DOT

%{
type type_args =
  | TA_args of raw_mod gen_type_expr list
  | TA_int  of int * Lexing.position * Lexing.position

let parse_error e loc =
  raise (Error (e, loc))

let make_var v =
  let s = Location.value v in
  let l = Location.loc v in
  Location.mk_loc_val (s, ()) l

let make_opt_var o =
  match o with
    | None   -> None
    | Some v -> Some (make_var v)

let make_int_literal s =
  let (s, n), loc = (Location.value s), (Location.loc s) in
  let i = try  int_of_string s
          with _ -> parse_error (Invalid_integer s) loc in
  if   not (AstUtils.check_int_literal n i)
  then parse_error (Invalid_integer_literal (i, n)) loc;
  i, n

let make_raw_int s =
  let s, loc = (Location.value s), (Location.loc s) in
  try  int_of_string s
  with _ -> parse_error (Invalid_integer s) loc

let make_bitvector_literal s =
  let len = String.length s in
  let s = String.sub s 2 (len - 2) in
  let l =
    Seq.fold_left (fun l c ->
        let b = match c with
            | '0' -> false
            | '1' -> true
            | _   -> assert false in
        b :: l
      ) [] (String.to_seq s) in
  List.rev l

let make_bitint n b e =
  register_bitwidth n;
  let l = Location.mk_loc b e in
  Location.mk_loc_val n l

let make_type_expr t b e =
  {type_expr     = t;
   type_expr_loc = Location.mk_loc b e}

let make_type c args s e =
  match c, args with
    | (None,   id), None ->
        AstUtils.make_raw_tname_id id
    | (Some m, id), None ->
        AstUtils.make_raw_mod_tname_id m id
    | (None,   id), Some (TA_args l) ->
        let c = AstUtils.make_raw_tname_id id in
        make_type_expr (TE_tapp (c, l)) s e
    | (Some m, id), Some (TA_args l) ->
        let c = AstUtils.make_raw_mod_tname_id m id in
        make_type_expr (TE_tapp (c, l)) s e
    | (None, id),   Some (TA_int (i, si, ei)) ->
        let tc = Location.value id in
        let li = Location.mk_loc si ei in
        if   tc <> "bitvector"
        then let err = Invalid_bitvector_constructor tc in
             parse_error err (Location.loc id)
        else if i <= 0
        then let err = Nonpositive_bitvector_width i in
             parse_error err li
        else let n = string_of_int i in
             let n = Location.mk_loc_val n li in
             let n = AstUtils.make_raw_tname_id n in
             let t = AstUtils.make_raw_tname_id id in
             register_bitwidth i;
             make_type_expr (TE_tapp (t, [n])) s e
    | (Some _, id), Some (TA_int _) ->
        let tc = Location.value id in
        let err = Invalid_bitvector_constructor tc in
        parse_error err (Location.loc id)

let make_unit_type b e =
  let loc = Location.mk_loc b e in
  AstUtils.make_raw_type_app "unit" [] loc

let conv_constr (m, t, c) =
  (Modul m, t, c)

let make_pattern pat b e =
  {pattern     = pat;
   pattern_loc = Location.mk_loc b e;
   pattern_aux = ()}

let make_type_rep tr b e =
  {type_rep     = tr;
   type_rep_loc = Location.mk_loc b e}

let make_expr exp b e =
  {expr     = exp;
   expr_loc = Location.mk_loc b e;
   expr_aux = ()}

let make_stmt s b e =
  {stmt     = s;
   stmt_loc = Location.mk_loc b e}

let make_action sl b e =
  {action_stmts = sl;
   action_loc   = Location.mk_loc b e}

let make_literal_set ls b e =
  {literal_set     = ls;
   literal_set_loc = Location.mk_loc b e}

let make_regexp re b e =
  {regexp     = re;
   regexp_mod = get_cur_module ();
   regexp_loc = Location.mk_loc b e;
   regexp_aux = ()}

let make_rule_elem re b e =
  {rule_elem     = re;
   rule_elem_mod = get_cur_module ();
   rule_elem_loc = Location.mk_loc b e;
   rule_elem_aux = ()}

let make_rule t res b e =
  {rule_temps = t;
   rule_rhs   = res;
   rule_loc   = Location.mk_loc b e}

let make_nt_defn n v inh syn r b e =
  {non_term_name      = n;
   non_term_varname   = v;
   non_term_inh_attrs = inh;
   non_term_syn_attrs = syn;
   non_term_rules     = r;
   non_term_mod       = get_cur_module ();
   non_term_loc       = Location.mk_loc b e}

let make_type_decl n k tvs bd b e =
  {type_decl_ident = n;
   type_decl_kind  = k;
   type_decl_tvars = tvs;
   type_decl_body  = bd;
   type_decl_mod   = get_cur_module ();
   type_decl_loc   = Location.mk_loc b e}

let make_fun_defn n r tvs p t bd b e =
  {fun_defn_ident     = n;
   fun_defn_tvars     = tvs;
   fun_defn_params    = p;
   fun_defn_res_type  = t;
   fun_defn_body      = bd;
   fun_defn_recursive = r;
   fun_defn_synth     = false;
   fun_defn_mod       = get_cur_module ();
   fun_defn_loc       = Location.mk_loc b e;
   fun_defn_aux       = ()}

let make_recfuns fs b e =
  {recfuns     = fs;
   recfuns_loc = Location.mk_loc b e}

let make_const_defn n t v b e =
  {const_defn_ident = n;
   const_defn_type  = t;
   const_defn_val   = v;
   const_defn_loc   = Location.mk_loc b e;
   const_defn_mod   = get_cur_module ();
   const_defn_aux   = ()}

let make_format_decl d a b e =
  {format_decl     = d;
   format_deco     = a;
   format_decl_loc = Location.mk_loc b e}

let make_deco t v a b e =
  {deco_type  = t;
   deco_value = v;
   deco_args  = a;
   deco_loc   = Location.mk_loc b e}

let make_format decls b e =
  {format_decls = decls;
   format_loc   = Location.mk_loc b e}

let make_ffi_decl f p r ls b e =
  AstUtils.check_lang_bindings ls;
  {ffi_decl_ident    = f;
   ffi_decl_params   = p;
   ffi_decl_res_type = r;
   ffi_decl_langs    = ls;
   ffi_decl_mod      = get_cur_module ();
   ffi_decl_loc      = Location.mk_loc b e;
   ffi_decl_aux      = ()}

(* Type expressions with syntactic support, such as tuples and lists,
   need support in the parser. *)

let make_list_type a b e =
  let loc = Location.mk_loc b e in
  AstUtils.make_raw_type_app "[]" [a] loc

let rec make_tuple_type l =
  match l with
    | [] -> assert false
    | [a] -> a
    | h :: rest ->
          let t   = make_tuple_type rest in
          let loc = Location.extent h.type_expr_loc t.type_expr_loc in
          AstUtils.make_raw_type_app "*" [h; t] loc

let rec make_tuple_pattern l =
  match l with
    | [] -> assert false
    | [a] -> a
    | h :: rest ->
        let p   = make_tuple_pattern rest in
        let loc = Location.extent h.pattern_loc p.pattern_loc in
        let t   = Location.mk_loc_val "*" loc in
        let c   = Location.mk_loc_val "_Tuple" loc in
        AstUtils.make_pattern_loc (P_variant ((Modul None, t, c), [h; p])) loc

let make_variant (c, l) s e =
  let loc = Location.mk_loc s e in
  match l with
    | [] -> c, None
    | _  -> c, Some (AstUtils.make_raw_arrow_type l loc)

let generate_kind tvs =
  List.fold_left (fun acc _ ->
      KArrow (KStar, acc)
    ) KStar tvs
%}

%%

ident:
| i=ID
  { i }

def:
| d=UID
| d=ident
  { d }

raw_int:
| i=RAW_INT
  { make_raw_int i }
| l=raw_int POS r=raw_int
  { l + r }
| l=raw_int NEG r=raw_int
  { l - r }
| l=raw_int STAR r=raw_int
  { l * r }
| LPAREN i=raw_int RPAREN
  { i }

type_id:
| i=ident
  { (None, i) }
| m=UID DOT i=ident
  { (Some m, i) }

type_args:
| LANGLE l=separated_list(COMMA, type_expr) RANGLE
  { TA_args l }
| LANGLE i=raw_int RANGLE
  { TA_int (i, $startpos(i), $endpos(i)) }

type_expr:
| tv=TVAR
  { AstUtils.make_tvar tv }
| LPAREN l=separated_list(COMMA, type_expr) RPAREN
  { if   List.length l = 0
    then make_unit_type $startpos $endpos
    else if List.length l = 1
    then List.nth l 0
    else make_tuple_type l }
| LBRACK t=type_expr RBRACK
  { make_list_type t $startpos $endpos }
| tc=type_id args=option(type_args)
  { make_type tc args $startpos $endpos }

variant:
| i=UID
  { make_variant (i, []) $startpos $endpos }
| i=UID OF l=separated_list(STAR, type_expr)
  { make_variant (i, l) $startpos $endpos }

variants:
| BAR l=separated_nonempty_list(BAR, variant)
  { l }

param_decl:
| i=ident COLON t=type_expr
  { (make_var i, t, ()) }

param_decls:
| l=separated_list(COMMA, param_decl)
  { l }

temp_decl:
| i=ident COLON t=type_expr COLONEQ e=expr
  { (make_var i, t, e) }

temp_decls:
| l=separated_list(COMMA, temp_decl)
  { l }

rec_typ_field:
| i=ident COLON t=type_expr
  { (i, t) }

rec_typ_fields:
| l=separated_list(COMMA, rec_typ_field)
  { l }

bit_range_field:
| i=ident COLON n=raw_int
  { let n = make_bitint n $startpos(n) $endpos(n) in
    (i, (n, n)) }
| i=ident COLON n=raw_int COLON m=raw_int
  { register_bitwidth (max n m);
    let l = Location.mk_loc $startpos(n) $endpos(n) in
    let n = Location.mk_loc_val n l in
    let l = Location.mk_loc $startpos(m) $endpos(m) in
    let m = Location.mk_loc_val m l in
    (i, (n, m)) }

bit_range_fields:
| l=separated_list(COMMA, bit_range_field)
  { l }

rec_exp_field:
| i=ident COLON e=expr
  { ((Modul None, i), e) }
| m=UID DOT i=ident COLON e=expr
  { ((Modul (Some m), i), e) }

rec_exp_fields:
| l=separated_nonempty_list(COMMA, rec_exp_field)
  { l }

listelems:
| hd=expr _s=SEMICOLON tl=listelems
  { let loc = Location.mk_loc $startpos(_s) $endpos(_s) in
    let t = Location.mk_loc_val "[]" loc in
    let c = Location.mk_loc_val "::" loc in
    make_expr (E_constr ((Modul None, t, c), [hd; tl])) $startpos $endpos }
| e=expr _s=RBRACK
  { let loc = Location.mk_loc $startpos $endpos in
    let t  = Location.mk_loc_val "[]" loc in
    let nl = Location.mk_loc_val "[]" loc in
    let co = Location.mk_loc_val "::" loc in
    let c  = Modul None, t, nl in
    let tl = make_expr (E_constr (c, [])) $startpos(_s) $endpos(_s) in
    let c  = Modul None, t, co in
    make_expr (E_constr (c, [e; tl])) $startpos $endpos }
| RBRACK
  { let loc = Location.mk_loc $startpos $endpos in
    let t = Location.mk_loc_val "[]" loc in
    let c = Location.mk_loc_val "[]" loc in
    make_expr (E_constr ((Modul None, t, c), [])) $startpos $endpos }

expr:
| v=ident
  { make_expr (E_var (make_var v)) $startpos $endpos }
| r=ident ARROW rop=ident LPAREN e=expr RPAREN
  { make_expr (E_recop ((Modul None, r, rop), e)) $startpos $endpos }
/* TODO: module syntax: this causes a shift/reduce conflict with E_mod_member
| LPAREN m=UID DOT r=ident RPAREN ARROW rop=ident LPAREN e=expr RPAREN
  { make_expr (E_recop ((Modul (Some m), r, rop), e)) $startpos $endpos }
*/
| u=UID DOT m=ident
  { make_expr (E_mod_member (u, m)) $startpos $endpos }
| e=expr DOT f=ident
  { make_expr (E_field (e, (Modul None, f))) $startpos $endpos }
| e=expr DOT LPAREN m=UID DOT f=ident RPAREN
  { make_expr (E_field (e, (Modul (Some m), f))) $startpos $endpos }
| l=LITERAL
  { make_expr (E_literal (PL_bytes (Location.value l))) $startpos $endpos }
| l=INT_LITERAL
  { let i, n = make_int_literal l in
    make_expr (E_literal (PL_int (i, n))) $startpos $endpos }
| b=BV_LITERAL
  { let b = make_bitvector_literal (Location.value b) in
    make_expr (E_literal (PL_bitvector b)) $startpos $endpos }
| LBRACKRBRACK
  { let loc = Location.mk_loc $startpos $endpos in
    let t = Location.mk_loc_val "[]" loc in
    let c = Location.mk_loc_val "[]" loc in
    make_expr (E_constr ((Modul None, t, c), [])) $startpos $endpos }
| LPAREN l=separated_list(COMMA, expr) RPAREN
  { let loc = Location.mk_loc $startpos $endpos in
    let t = Location.mk_loc_val "*" loc in
    let c = Location.mk_loc_val "_Tuple" loc in
    if List.length l = 0
    then make_expr (E_literal PL_unit) $startpos $endpos
    else if List.length l = 1
    then List.nth l 0
    else make_expr (E_constr ((Modul None, t, c), l)) $startpos $endpos }
| PRINT  LPAREN e=expr RPAREN
  { make_expr (E_print (false, e)) $startpos $endpos }
| PRINTT LPAREN e=expr RPAREN
  { make_expr (E_print (true, e)) $startpos $endpos }
| e=expr LPAREN l=separated_list(COMMA, expr) RPAREN
  { make_expr (E_apply(e, l)) $startpos $endpos }
| e=expr LBRACK i=expr RBRACK
  { make_expr (E_binop(Index, e, i)) $startpos $endpos }
| e=expr LLBRACK n=raw_int COLON m=raw_int RRBRACK
  { make_expr (E_bitrange(e, n, m)) $startpos $endpos }
| e=expr LLBRACK n=raw_int RRBRACK
  { make_expr (E_bitrange(e, n, n)) $startpos $endpos }
| c=CONSTR LPAREN l=separated_list(COMMA, expr) RPAREN
  { make_expr (E_constr(conv_constr c, l)) $startpos $endpos }
| n=MINUS e=expr %prec UMINUS
  { make_expr (E_unop (Uminus n, e)) $startpos $endpos }
| TILDE e=expr %prec UMINUS
  { make_expr (E_unop (Neg_b, e)) $startpos $endpos }
| n=IB_NOT e=expr %prec UMINUS
  { make_expr (E_unop (Inot n, e)) $startpos $endpos }
| EXCLAIM e=expr
  { make_expr (E_unop (Not, e)) $startpos $endpos }
| LBRACE r=rec_exp_fields RBRACE
  { make_expr (E_record r) $startpos $endpos }
| l=expr LAND r=expr
  { make_expr (E_binop (Land, l, r)) $startpos $endpos }
| l=expr LOR r=expr
  { make_expr (E_binop (Lor, l, r)) $startpos $endpos }
| e=expr CONSTR_MATCH c=CONSTR
  { make_expr (E_match (e, conv_constr c)) $startpos $endpos }
| l=expr PLUS_S r=expr
  { make_expr (E_binop (Plus_s, l, r)) $startpos $endpos }
| l=expr BAR_B r=expr
  { make_expr (E_binop (Or_b, l, r)) $startpos $endpos }
| l=expr AND_B r=expr
  { make_expr (E_binop (And_b, l, r)) $startpos $endpos }
| l=expr n=PLUS r=expr
  { make_expr (E_binop (Plus n, l, r)) $startpos $endpos }
| l=expr AT r=expr
  { make_expr (E_binop (At, l, r)) $startpos $endpos }
| l=expr n=MINUS r=expr
  { make_expr (E_binop (Minus n, l, r)) $startpos $endpos }
| l=expr n=MUL r=expr
  { make_expr (E_binop (Mult n, l, r)) $startpos $endpos }
| l=expr n=MOD r=expr
  { make_expr (E_binop (Mod n, l, r)) $startpos $endpos }
| l=expr n=DIV r=expr
  { make_expr (E_binop (Div n, l, r)) $startpos $endpos }
| l=expr n=IB_AND r=expr
  { make_expr (E_binop (Iand n, l, r)) $startpos $endpos }
| l=expr n=IB_OR r=expr
  { make_expr (E_binop (Ior n, l, r)) $startpos $endpos }
| l=expr n=IB_XOR r=expr
  { make_expr (E_binop (Ixor n, l, r)) $startpos $endpos }
| l=expr n=LSHFT r=expr
  { make_expr (E_binop (Lshft n, l, r)) $startpos $endpos }
| l=expr n=RSHFT r=expr
  { make_expr (E_binop (Rshft n, l, r)) $startpos $endpos }
| l=expr n=ASHFT r=expr
  { make_expr (E_binop (Ashft n, l, r)) $startpos $endpos }
| l=expr n=LT r=expr
  { make_expr (E_binop (Lt n, l, r)) $startpos $endpos }
| l=expr n=GT r=expr
  { make_expr (E_binop (Gt n, l, r)) $startpos $endpos }
| l=expr n=LTEQ r=expr
  { make_expr (E_binop (Lteq n, l, r)) $startpos $endpos }
| l=expr n=GTEQ r=expr
  { make_expr (E_binop (Gteq n, l, r)) $startpos $endpos }
| l=expr EQ r=expr
  { make_expr (E_binop (Eq, l, r)) $startpos $endpos }
| l=expr NEQ r=expr
  { make_expr (E_binop (Neq, l, r)) $startpos $endpos }
| l=expr COLONCOLON r=expr
  { make_expr (E_binop (Cons, l, r)) $startpos $endpos }
| LBRACK l=listelems
  { l }
| LPAREN CASE e=expr OF option(BAR) b=separated_list(BAR, branch) RPAREN
  { make_expr (E_case (e, b)) $startpos $endpos }
| LET p=pattern EQ e=expr IN b=expr
  { make_expr (E_let (p, e, b)) $startpos $endpos }
| LPAREN e=expr COLON t=type_expr RPAREN
  { make_expr (E_cast (e, t)) $startpos $endpos }

pattern:
| UNDERSCORE
  { make_pattern P_wildcard $startpos $endpos }
| v=ident
  { make_pattern (P_var (make_var v)) $startpos $endpos }
| LBRACKRBRACK
  { let loc = Location.mk_loc $startpos $endpos in
    let t = Location.mk_loc_val "[]" loc in
    let c = Location.mk_loc_val "[]" loc in
    let p = P_variant ((Modul None, t, c), []) in
    make_pattern p $startpos $endpos }
| hd=pattern COLONCOLON tl=pattern
  { let loc = Location.mk_loc $startpos $endpos in
    let t = Location.mk_loc_val "[]" loc in
    let c = Location.mk_loc_val "::" loc in
    let p = P_variant ((Modul None, t, c), [hd; tl]) in
    make_pattern p $startpos $endpos }
| c=CONSTR a=option(pattern_args)
  { let pat = match a with
        | None   -> P_variant (conv_constr c, [])
        | Some l -> P_variant (conv_constr c, l) in
    make_pattern pat $startpos $endpos }
| l=LITERAL
  { make_pattern (P_literal (PL_bytes (Location.value l))) $startpos $endpos }
| l=INT_LITERAL
  { let i, n = make_int_literal l in
    make_pattern (P_literal (PL_int (i, n))) $startpos $endpos }
| ps=pattern_args
  { if List.length ps = 0
    then make_pattern (P_literal PL_unit) $startpos $endpos
    else if List.length ps = 1
    then List.hd ps
    else make_tuple_pattern ps }

pattern_args:
| LPAREN ps=separated_list(COMMA, pattern) RPAREN
  { ps }

branch:
| p=pattern ARROW e=expr
  { (p, e) }

assign_lhs_expr:
| v=ident
  { make_expr (E_var (make_var v)) $startpos $endpos }
| e=assign_lhs_expr DOT f=ident
  { make_expr (E_field (e, (Modul None, f))) $startpos $endpos }
| e=assign_lhs_expr LBRACK i=expr RBRACK
  { make_expr (E_binop (Index, e, i)) $startpos $endpos }

stmt:
| l=assign_lhs_expr COLONEQ r=expr
  { make_stmt (S_assign (l, r)) $startpos $endpos }
| LET p=pattern EQ e=expr IN s=stmt
  { make_stmt (S_let (p, e, [s])) $startpos $endpos }
| LET p=pattern EQ e=expr IN LBRACE s=separated_list(SEMICOLON, stmt) RBRACE
  { make_stmt (S_let (p, e, s)) $startpos $endpos }
| LPAREN CASE e=expr OF option(BAR) c=separated_list(BAR, branchstmt) RPAREN
  { make_stmt (S_case (e, c)) $startpos $endpos }
| PRINT  LPAREN e=expr RPAREN
  { make_stmt (S_print (false, e)) $startpos $endpos }
| PRINTT LPAREN e=expr RPAREN
  { make_stmt (S_print (true, e)) $startpos $endpos }

branchstmt:
| p=pattern ARROW s=stmt
  { (p, [s]) }
| p=pattern ARROW LBRACE s=separated_nonempty_list(SEMICOLON, stmt) RBRACE
  { (p, s) }

action:
| sl=separated_list(SEMICOLON, stmt)
  { make_action (sl, None) $startpos $endpos }
| sl=separated_list(SEMICOLON, stmt) SEMISEMI e=expr
  { make_action (sl, Some e) $startpos $endpos }

literal_set:
| t=UID
  { make_literal_set (LS_type (Modul None, t)) $startpos $endpos }
| m=UID DOT t=UID
  { make_literal_set (LS_type (Modul (Some m), t)) $startpos $endpos }
| l=separated_nonempty_list(BAR, LITERAL)
  { make_literal_set (LS_set l) $startpos $endpos }
| l=literal_set BACKSLASH r=literal_set
  { make_literal_set (LS_diff (l, r)) $startpos $endpos }
| b=LITERAL DOTDOT e=LITERAL
  { make_literal_set (LS_range (b, e)) $startpos $endpos }
| LPAREN l=literal_set RPAREN
  { l }

regexp:
| LBRACK l=literal_set RBRACK
  { make_regexp (RX_literals l) $startpos $endpos }
| HASH
  { make_regexp RX_wildcard $startpos $endpos }
| i=UID
  { make_regexp  (RX_type (Modul None, i)) $startpos $endpos }
| m=UID DOT i=UID
  { make_regexp  (RX_type (Modul (Some m), i)) $startpos $endpos }
| r=regexp STAR
  { make_regexp  (RX_star (r, None)) $startpos $endpos }
| r=regexp CARET e=expr
  { make_regexp  (RX_star (r, Some e)) $startpos $endpos }
| r=regexp POS
  { let k = make_regexp (RX_star (r, None)) $startpos $endpos in
    make_regexp (RX_seq [r; k]) $startpos $endpos }
| r=regexp QUESTION
  { make_regexp (RX_opt r) $startpos $endpos }
| l=regexp BAR r=regexp
  { make_regexp (RX_choice [l; r]) $startpos $endpos }
| LPAREN l=list(regexp) RPAREN
  { make_regexp (RX_seq l) $startpos $endpos }

nt_attr_val:
| i=ident EQ v=expr
  { (i, A_eq, v) }
| i=ident LARROW LPAREN v=expr RPAREN
  { (i, A_in, v) }

nt_args:
| LANGLE inh=separated_list(COMMA, nt_attr_val) RANGLE
  { inh }

rule_elem:
| EPSILON
  { make_rule_elem RE_epsilon $startpos $endpos }
| SYN_BEGIN l=nonempty_list(regexp) SYN_END
  { let r = make_regexp (RX_seq l) $startpos(l) $endpos(l) in
    make_rule_elem (RE_regexp r) $startpos $endpos }
| EXCLAIM s=list(literal_set) EXCLAIM
  { let l =
      List.map (fun l ->
          make_regexp (RX_literals l) $startpos(s) $endpos(s)
        ) s in
    let r = make_regexp (RX_seq l) $startpos(s) $endpos(s) in
    make_rule_elem (RE_regexp r) $startpos $endpos }
| nt=UID inh=option(nt_args)
  { let id = Location.value nt in
    if id = "BitVector"
    then let err = if inh = None
                   then Missing_bitvector_width
                   else Invalid_bitvector_syntax in
         parse_error err (Location.loc nt)
    else make_rule_elem (RE_non_term (Modul None, nt, inh)) $startpos $endpos }
| m=UID DOT nt=UID inh=option(nt_args)
  { make_rule_elem (RE_non_term (Modul (Some m), nt, inh)) $startpos $endpos }
| nt=UID LANGLE i=raw_int RANGLE
  { let id = Location.value nt in
    if id <> "BitVector"
    then let err = Invalid_bitvector_nonterminal id in
         parse_error err (Location.loc nt)
    else let i = make_bitint i $startpos(i) $endpos(i) in
         make_rule_elem (RE_bitvector i) $startpos $endpos }
| ALIGN LANGLE i=raw_int RANGLE
  { let i = make_bitint i $startpos(i) $endpos(i) in
    make_rule_elem (RE_align i) $startpos $endpos }
| PAD LANGLE i=raw_int COMMA b=BV_LITERAL RANGLE
  { let b = make_bitvector_literal (Location.value b) in
    let i = make_bitint i $startpos(i) $endpos(i) in
    make_rule_elem (RE_pad (i, b)) $startpos $endpos }
| USE_BITFIELD LPAREN i=ident RPAREN
  { make_rule_elem (RE_bitfield i) $startpos $endpos }
| LBRACK e=expr RBRACK
  { make_rule_elem (RE_constraint e) $startpos $endpos }
| LBRACE a=action RBRACE
  { make_rule_elem (RE_action a) $startpos $endpos }
| l=rule_elem BAR r=rule_elem
  { make_rule_elem (RE_choice [l; r]) $startpos $endpos }
| r=rule_elem STAR
  { make_rule_elem (RE_star (r, None)) $startpos $endpos }
| r=rule_elem CARET e=expr
  { make_rule_elem (RE_star (r, Some e)) $startpos $endpos }
| v=ident EQ r=rule_elem
  { make_rule_elem (RE_named ((make_var v), r)) $startpos $endpos }
| LPAREN l=list(rule_elem) RPAREN
  { if   List.length l == 1
    then List.nth l 0
    else make_rule_elem (RE_seq l) $startpos $endpos }
| r=rule_elem POS
  { let k = make_rule_elem (RE_star (r, None)) $startpos $endpos in
    make_rule_elem (RE_seq [r; k]) $startpos $endpos }
| r=rule_elem QUESTION
  { make_rule_elem (RE_opt r) $startpos $endpos }
| AT_POS e=expr COMMA r=rule_elem RPAREN
  { make_rule_elem (RE_at_pos (e, r)) $startpos $endpos }
| AT_VIEW e=expr COMMA r=rule_elem RBRACK
  { make_rule_elem (RE_at_view (e, r)) $startpos $endpos }
| AT_MAP e=expr COMMA r=rule_elem RBRACK
  { make_rule_elem (RE_map_views (e, r)) $startpos $endpos }
| SET_VIEW e=expr RBRACK
  { make_rule_elem (RE_set_view e) $startpos $endpos }
| SLASH_SF_LBRACK s=LITERAL RBRACK
  { make_rule_elem (RE_scan (s, Scan_forward)) $startpos $endpos }
| SLASH_SB_LBRACK s=LITERAL RBRACK
  { make_rule_elem (RE_scan (s, Scan_backward)) $startpos $endpos }
| LSRCO i=ident LPAREN l=separated_list(COMMA, expr) RPAREN RSRCO
  { make_rule_elem (RE_suspend_resume (i, l)) $startpos $endpos }

rule:
| LPARBAR d=temp_decls RPARBAR l=list(rule_elem)
  { make_rule d l $startpos $endpos }
| l=list(rule_elem)
  { make_rule [] l $startpos $endpos }

nt_attr_decl:
| i=ident COLON t=type_expr
  { (i, t, (), None) }
| i=ident COLON t=type_expr COLONEQ e=expr
  { (i, t, (), Some e) }

nt_attr_decls:
| l=separated_list(COMMA, nt_attr_decl)
  { l }

nt_param_decls:
| d=nt_attr_decls
  { ALT_decls d }
| i=ident
  { ALT_type i }

nt_defn:
| n=UID v=option(ident) COLONEQ
  r=separated_nonempty_list(SEMICOLON, rule)
  { make_nt_defn n (make_opt_var v) [] (ALT_decls []) r $startpos $endpos }
| n=UID v=option(ident)
  LBRACE syn=nt_param_decls RBRACE COLONEQ
  r=separated_nonempty_list(SEMICOLON, rule)
  { make_nt_defn n (make_opt_var v) [] syn r $startpos $endpos }
| n=UID v=option(ident)
  LPAREN inh=param_decls RPAREN COLONEQ
  r=separated_nonempty_list(SEMICOLON, rule)
  { make_nt_defn n (make_opt_var v) inh (ALT_decls []) r $startpos $endpos }
| n=UID v=option(ident)
  LPAREN inh=param_decls RPAREN
  LBRACE syn=nt_param_decls RBRACE COLONEQ
  r=separated_nonempty_list(SEMICOLON, rule)
  { make_nt_defn n (make_opt_var v) inh syn r $startpos $endpos }

deco_arg:
| k=ident EQ v=ident
  { Deco_keyvalue (k, v) }
| k=ident
  { Deco_key k }

deco_spec:
| a=ident LPAREN v=def COLON args=separated_list(COMMA, deco_arg) RPAREN
  { make_deco a v args $startpos $endpos }
| a=ident LPAREN v=def RPAREN RBRACK
  { make_deco a v [] $startpos $endpos }

deco_decl:
| DECO l=separated_list(SEMICOLON, deco_spec) RBRACK
  { l }

format_decl:
| a=option(deco_decl) d=nt_defn
  { make_format_decl d a $startpos $endpos }

/* TODO: add kind specs */
type_decl:
| t=ident EQ r=type_expr
  { let rep = make_type_rep (TR_defn r) $startpos $endpos in
    make_type_decl t KStar [] rep $startpos $endpos }
| t=ident LPAREN tvs=separated_list(COMMA, TVAR) RPAREN EQ r=type_expr
  { let rep = make_type_rep (TR_defn r) $startpos $endpos in
    make_type_decl t (generate_kind tvs) tvs rep $startpos $endpos }
| t=ident EQ vs=variants
  { let rep = make_type_rep (TR_variant vs) $startpos(vs) $endpos(vs) in
    make_type_decl t KStar [] rep $startpos $endpos }
| t=ident LPAREN tvs=separated_list(COMMA, TVAR) RPAREN EQ vs=variants
  { let rep = make_type_rep (TR_variant vs) $startpos(vs) $endpos(vs) in
    make_type_decl t (generate_kind tvs) tvs rep $startpos $endpos }
| t=ident EQ LBRACE r=rec_typ_fields RBRACE
  { let rep = make_type_rep (TR_record r) $startpos $endpos in
    make_type_decl t KStar [] rep $startpos $endpos }
| t=ident LPAREN tvs=separated_list(COMMA, TVAR) RPAREN EQ LBRACE r=rec_typ_fields RBRACE
  { let rep = make_type_rep (TR_record r) $startpos $endpos in
    make_type_decl t (generate_kind tvs) tvs rep $startpos $endpos }


bitfield:
| bf=ident EQ LBRACE r=bit_range_fields RBRACE
  { let rep = make_type_rep (TR_bitfield r) $startpos $endpos in
    make_type_decl bf KStar [] rep $startpos $endpos }

type_decls:
| BITFIELD b=bitfield
  { [b] }
| TYPE t=type_decl
  { [t] }
| TYPE t=type_decl AND l=separated_list(AND, type_decl)
  { t :: l }

fun_decl:
| f=ident LPAREN p=param_decls RPAREN ARROW r=type_expr EQ LBRACE e=expr RBRACE
  { make_fun_defn (make_var f) false [] p r e $startpos $endpos }
| f=ident LANGLE tvs=separated_list(COMMA, TVAR) RANGLE
    LPAREN p=param_decls RPAREN ARROW r=type_expr EQ LBRACE e=expr RBRACE
  { make_fun_defn (make_var f) false tvs p r e $startpos $endpos }

recfun_decl:
| f=ident LPAREN p=param_decls RPAREN ARROW r=type_expr EQ LBRACE e=expr RBRACE
  { make_fun_defn (make_var f) true [] p r e $startpos $endpos }
| f=ident LANGLE tvs=separated_list(COMMA, TVAR) RANGLE
    LPAREN p=param_decls RPAREN ARROW r=type_expr EQ LBRACE e=expr RBRACE
  { make_fun_defn (make_var f) true tvs p r e $startpos $endpos }

ffispec:
| l=ident EQ f=LITERAL
  { (l, f) }

ffifun:
| LBRACE ls=separated_nonempty_list(COMMA, ffispec) RBRACE
  f=ident LPAREN p=param_decls RPAREN ARROW r=type_expr
  { make_ffi_decl (make_var f) p r ls $startpos $endpos }

pre_decl:
| INCLUDE m=def
  { PDecl_include [m] }
| INCLUDE LBRACE m=separated_list(COMMA, def) RBRACE
  { PDecl_include m }
| IMPORT m=UID
  { PDecl_import [m] }
| IMPORT LBRACE m=separated_list(COMMA, UID) RBRACE
  { PDecl_import m }
| l=type_decls
  { PDecl_types (l, Location.mk_loc $startpos $endpos) }
| CONST c=ident COLON t=type_expr EQ e=expr
  { PDecl_const (make_const_defn (make_var c) t e $startpos $endpos) }
| FUN f=fun_decl
  { PDecl_fun f }
| RECFUN fs=separated_nonempty_list(AND, recfun_decl)
  { PDecl_recfuns (make_recfuns fs $startpos $endpos) }
| FORMAT LBRACE d=separated_list(SEMISEMI, format_decl) RBRACE
  { PDecl_format (make_format d $startpos $endpos) }
| FOREIGN LBRACE fs=separated_nonempty_list(SEMICOLON, ffifun) RBRACE
  { PDecl_foreign fs }
toplevel:
| pre_decls=list(pre_decl) EOF
  { { pre_decls } }
