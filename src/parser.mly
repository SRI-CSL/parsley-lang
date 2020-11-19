%{
open Ast
open Parseerror
open AstUtils
%}

%token EOF
%token FORMAT TYPE AND FUN RECFUN USE OF CASE LET IN
%token ATTR
%token EPSILON

%token LBRACE RBRACE LPAREN RPAREN LBRACK RBRACK
%token LPARBAR RPARBAR SYN_BEGIN SYN_END
%token AT_POS AT_BUF AT_MAP HASH
%token BAR COMMA COLON COLONEQ SEMICOLON SEMISEMI DOT QUESTION ARROW
%token STAR PLUS MINUS DIV CARET PLUS_S AT
%token LT GT LTEQ GTEQ EQ NEQ LAND LOR
%token CONSTR_MATCH COLONCOLON BACKSLASH EXCLAIM UNDERSCORE DOTDOT

%token<Ast.literal> LITERAL
%token<Ast.ident>   ID
%token<Ast.ident>   UID
%token<Ast.tvar>    TVAR

%token<string Location.loc> INT_LITERAL

%token<string Location.loc * string Location.loc> CONSTR

%start<Ast.pre_top_level> toplevel

(* operators are increasing precedence order. *)
%nonassoc IN
%right EXCLAIM
%left  LAND LOR
%left  LT GT LTEQ GTEQ EQ NEQ CONSTR_MATCH
%left  BAR
%left  BACKSLASH
%right AT
%right COLONCOLON
%left  STAR DIV QUESTION
%left  PLUS MINUS PLUS_S
%left  CARET
%nonassoc UMINUS
%left  LPAREN LBRACK
%left  DOT

%{
let parse_error e loc =
  raise (Error (e, loc))

let make_int_literal s =
  let s, loc = (Location.value s), (Location.loc s) in
  try  int_of_string s
  with _ -> parse_error (Invalid_integer s) loc

let make_type_expr t b e =
  { type_expr = t;
    type_expr_loc = Location.mk_loc b e }

let make_type_app_ident ident args b e =
  let c = make_tvar_ident ident in
  { type_expr = TE_tapp (c, args);
    type_expr_loc = Location.mk_loc b e }

let make_pattern pat b e =
  { pattern = pat;
    pattern_loc = Location.mk_loc b e }

let make_type_rep tr b e =
  { type_rep = tr;
    type_rep_loc = Location.mk_loc b e }

let make_expr exp b e =
  { expr = exp;
    expr_loc = Location.mk_loc b e }

let make_stmt s b e =
  { stmt = s;
    stmt_loc = Location.mk_loc b e }

let make_action sl b e =
  { action_stmts = sl;
    action_loc = Location.mk_loc b e }

let make_literal_set ls b e =
  { literal_set = ls;
    literal_set_loc = Location.mk_loc b e }

let make_regexp re b e =
  { regexp = re;
    regexp_loc = Location.mk_loc b e }

let make_rule_elem re b e =
  { rule_elem = re;
    rule_elem_loc = Location.mk_loc b e }

let make_rule t res b e =
  { rule_temps = t;
    rule_rhs = res;
    rule_loc = Location.mk_loc b e }

let make_nt_defn n v inh syn r b e =
  { non_term_name = n;
    non_term_varname = v;
    non_term_inh_attrs = inh;
    non_term_syn_attrs = syn;
    non_term_rules = r;
    non_term_loc = Location.mk_loc b e }

let make_type_decl n k tvs bd b e =
  { type_decl_ident = n;
    type_decl_kind = k;
    type_decl_tvars = tvs;
    type_decl_body = bd;
    type_decl_loc = Location.mk_loc b e }

let make_fun_defn n r tvs p t bd b e =
  { fun_defn_ident = n;
    fun_defn_tvars = tvs;
    fun_defn_params = p;
    fun_defn_res_type = t;
    fun_defn_body = bd;
    fun_defn_recursive = r;
    fun_defn_loc = Location.mk_loc b e }

let make_use m b e =
  { use_modules = m;
    use_loc = Location.mk_loc b e }

let make_format_decl d a b e =
  { format_decl = d;
    format_attr = a;
    format_decl_loc = Location.mk_loc b e }

let make_attr t v a b e =
  { attr_type = t;
    attr_value = v;
    attr_args = a;
    attr_loc = Location.mk_loc b e }

let make_format decls b e =
  { format_decls = decls;
    format_loc = Location.mk_loc b e }

(* Type expressions with syntactic support, such as tuples and lists,
   need support in the parser. *)

let make_list_type a b e =
  let loc = Location.mk_loc b e in
  make_type_app_name "[]" [a] loc

let rec make_tuple_type l =
  match l with
    | [] -> assert false
    | [a] -> a
    | h :: rest ->
          let t = make_tuple_type rest in
          let loc = Location.extent h.type_expr_loc t.type_expr_loc in
          make_type_app_name "*" [h; t] loc

let rec make_tuple_pattern l =
  match l with
    | [] -> assert false
    | [a] -> a
    | h :: rest ->
        let p = make_tuple_pattern rest in
        let loc = Location.extent h.pattern_loc p.pattern_loc in
        let t = Location.mk_loc_val "*" loc in
        let c = Location.mk_loc_val "_Tuple" loc in
        make_pattern_loc (P_variant ((t, c), [h; p])) loc

let make_variant (c, l) s e =
  let loc = Location.mk_loc s e in
  match l with
    | [] -> c, None
    | _  -> c, Some (make_arrow_type l loc)

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

type_expr:
| tv=TVAR
  { make_tvar_ident tv }
| i=ident
  { make_type_app_ident i [] $startpos $endpos }
| LPAREN l=separated_list(COMMA, type_expr) RPAREN
  { if List.length l = 1
    then List.nth l 0
    else make_tuple_type l }
| LBRACK t=type_expr RBRACK
  { make_list_type t $startpos $endpos }
| d=def LT l=separated_list(COMMA, type_expr) GT
  { let c = make_tvar_ident d in
    make_type_expr (TE_tapp (c, l)) $startpos $endpos }

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
  { (i, t) }

param_decls:
| l=separated_list(COMMA, param_decl)
  { l }

temp_decl:
| i=ident COLON t=type_expr COLONEQ e=expr
  { (i, t, e) }

temp_decls:
| l=separated_list(COMMA, temp_decl)
  { l }

rec_typ_field:
| i=ident COLON t=type_expr
  { (i, t) }

rec_typ_fields:
| l=separated_list(COMMA, rec_typ_field)
  { l }

rec_exp_field:
| i=ident COLON e=expr
  { (i, e) }

rec_exp_fields:
| l=separated_nonempty_list(COMMA, rec_exp_field)
  { l }

listelems:
| hd=expr _s=SEMICOLON tl=listelems
  { let loc = Location.mk_loc $startpos(_s) $endpos(_s) in
    let t = Location.mk_loc_val "[]" loc in
    let c = Location.mk_loc_val "::" loc in
    make_expr (E_constr (t, c, [hd; tl])) $startpos $endpos }
| e=expr _s=RBRACK
  { let loc = Location.mk_loc $startpos $endpos in
    let t  = Location.mk_loc_val "[]" loc in
    let nl = Location.mk_loc_val "[]" loc in
    let co = Location.mk_loc_val "::" loc in
    let tl = make_expr (E_constr (t, nl, [])) $startpos(_s) $endpos(_s) in
    make_expr (E_constr (t, co, [e; tl])) $startpos $endpos }
| RBRACK
  { let loc = Location.mk_loc $startpos $endpos in
    let t = Location.mk_loc_val "[]" loc in
    let c = Location.mk_loc_val "[]" loc in
    make_expr (E_constr (t, c, [])) $startpos $endpos }

expr:
| i=ident
  { make_expr (E_var i) $startpos $endpos }
| u=UID DOT m=ident
  { make_expr (E_mod_member (u, m)) $startpos $endpos }
| e=expr DOT f=ident
  { make_expr (E_field (e, f)) $startpos $endpos }
| l=LITERAL
  { make_expr (E_literal (PL_string (Location.value l))) $startpos $endpos }
| l=INT_LITERAL
  { let i = make_int_literal l in
    make_expr (E_literal (PL_int i)) $startpos $endpos }
| LPAREN l=separated_list(COMMA, expr) RPAREN
  { let loc = Location.mk_loc $startpos $endpos in
    let t = Location.mk_loc_val "*" loc in
    let c = Location.mk_loc_val "_Tuple" loc in
    if List.length l = 0
    then make_expr (E_literal PL_unit) $startpos $endpos
    else if List.length l = 1
    then List.nth l 0
    else make_expr (E_constr (t, c, l)) $startpos $endpos }
| e=expr LPAREN l=separated_list(COMMA, expr) RPAREN
  { make_expr (E_apply(e, l)) $startpos $endpos }
| e=expr LBRACK i=expr RBRACK
  { make_expr (E_binop(Index, e, i)) $startpos $endpos }
| c=CONSTR LPAREN l=separated_list(COMMA, expr) RPAREN
  { make_expr (E_constr(fst c, snd c, l)) $startpos $endpos }
| MINUS e=expr %prec UMINUS
  { make_expr (E_unop (Uminus, e)) $startpos $endpos }
| EXCLAIM e=expr
  { make_expr (E_unop (Not, e)) $startpos $endpos }
| LBRACE r=rec_exp_fields RBRACE
  { make_expr (E_record r) $startpos $endpos }
| l=expr LAND r=expr
  { make_expr (E_binop (Land, l, r)) $startpos $endpos }
| l=expr LOR r=expr
  { make_expr (E_binop (Lor, l, r)) $startpos $endpos }
| e=expr CONSTR_MATCH c=CONSTR
  { make_expr (E_match (e, fst c, snd c)) $startpos $endpos }
| l=expr PLUS r=expr
  { make_expr (E_binop (Plus, l, r)) $startpos $endpos }
| l=expr PLUS_S r=expr
  { make_expr (E_binop (Plus_s, l, r)) $startpos $endpos }
| l=expr AT r=expr
  { make_expr (E_binop (At, l, r)) $startpos $endpos }
| l=expr MINUS r=expr
  { make_expr (E_binop (Minus, l, r)) $startpos $endpos }
| l=expr STAR r=expr
  { make_expr (E_binop (Mult, l, r)) $startpos $endpos }
| l=expr DIV r=expr
  { make_expr (E_binop (Div, l, r)) $startpos $endpos }
| l=expr LT r=expr
  { make_expr (E_binop (Lt, l, r)) $startpos $endpos }
| l=expr GT r=expr
  { make_expr (E_binop (Gt, l, r)) $startpos $endpos }
| l=expr LTEQ r=expr
  { make_expr (E_binop (Lteq, l, r)) $startpos $endpos }
| l=expr GTEQ r=expr
  { make_expr (E_binop (Gteq, l, r)) $startpos $endpos }
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
  { make_pattern (P_var v) $startpos $endpos }
| v=CONSTR a=option(pattern_args)
  { let pat = match a with
        | None   -> P_variant (v, [])
        | Some l -> P_variant (v, l)
    in make_pattern pat $startpos $endpos }
| l=LITERAL
  { make_pattern (P_literal (PL_string (Location.value l))) $startpos $endpos }
| l=INT_LITERAL
  { let i = make_int_literal l in
    make_pattern (P_literal (PL_int i)) $startpos $endpos }
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
  { make_expr (E_var v) $startpos $endpos }
| e=assign_lhs_expr DOT f=ident
  { make_expr (E_field (e, f)) $startpos $endpos }
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
  { make_literal_set (LS_type t) $startpos $endpos }
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
  { make_regexp  (RX_type i) $startpos $endpos }
| r=regexp STAR
  { make_regexp  (RX_star (r, None)) $startpos $endpos }
| r=regexp CARET e=expr
  { make_regexp  (RX_star (r, Some e)) $startpos $endpos }
| r=regexp PLUS
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
  { (i, v) }

nt_args:
| LT inh=separated_list(COMMA, nt_attr_val) GT
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
  { make_rule_elem (RE_non_term (nt, inh)) $startpos $endpos }
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
  { make_rule_elem (RE_named (v, r)) $startpos $endpos }
| LPAREN l=list(rule_elem) RPAREN
  { if   List.length l == 1
    then List.nth l 0
    else make_rule_elem (RE_seq l) $startpos $endpos }
| r=rule_elem PLUS
  { let k = make_rule_elem (RE_star (r, None)) $startpos $endpos in
    make_rule_elem (RE_seq [r; k]) $startpos $endpos }
| r=rule_elem QUESTION
  { make_rule_elem (RE_opt r) $startpos $endpos }
| AT_POS e=expr COMMA r=rule_elem RPAREN
  { make_rule_elem (RE_at_pos (e, r)) $startpos $endpos }
| AT_BUF e=expr COMMA r=rule_elem RBRACK
  { make_rule_elem (RE_at_buf (e, r)) $startpos $endpos }
| AT_MAP e=expr COMMA r=rule_elem RBRACK
  { make_rule_elem (RE_map_bufs (e, r)) $startpos $endpos }

rule:
| LPARBAR d=temp_decls RPARBAR l=list(rule_elem)
  { make_rule d l $startpos $endpos }
| l=list(rule_elem)
  { make_rule [] l $startpos $endpos }

nt_param_decls:
| d=param_decls
  { ALT_decls d }
| i=ident
  { ALT_type i }

nt_defn:
| n=UID v=option(ident) COLONEQ
  r=separated_nonempty_list(SEMICOLON, rule)
  { make_nt_defn n v [] (ALT_decls []) r $startpos $endpos }
| n=UID v=option(ident)
  LBRACE syn=nt_param_decls RBRACE COLONEQ
  r=separated_nonempty_list(SEMICOLON, rule)
  { make_nt_defn n v [] syn r $startpos $endpos }
| n=UID v=option(ident)
  LPAREN inh=param_decls RPAREN COLONEQ
  r=separated_nonempty_list(SEMICOLON, rule)
  { make_nt_defn n v inh (ALT_decls []) r $startpos $endpos }
| n=UID v=option(ident)
  LPAREN inh=param_decls RPAREN
  LBRACE syn=nt_param_decls RBRACE COLONEQ
  r=separated_nonempty_list(SEMICOLON, rule)
  { make_nt_defn n v inh syn r $startpos $endpos }

attr_arg:
| k=ident EQ v=ident
  { Attr_keyvalue (k, v) }
| k=ident
  { Attr_key k }

attr_decl:
| ATTR a=ident LPAREN v=def COLON args=separated_list(COMMA, attr_arg) RPAREN RBRACK
  { make_attr a v args $startpos $endpos }
| ATTR a=ident LPAREN v=def RPAREN RBRACK
  { make_attr a v [] $startpos $endpos }

format_decl:
| a=option(attr_decl) d=nt_defn
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

type_decls:
| TYPE t=type_decl
  { [t] }
| TYPE t=type_decl AND l=separated_list(AND, type_decl)
  { t :: l }

pre_decl:
| USE m=ident
  { PDecl_use (make_use [m] $startpos $endpos) }
| USE LBRACE m=separated_list(COMMA, ident) RBRACE
  { PDecl_use (make_use m $startpos $endpos) }
| l=type_decls
  { PDecl_types (l, Location.mk_loc $startpos $endpos) }
| FUN f=ident LPAREN p=param_decls RPAREN ARROW r=type_expr EQ LBRACE e=expr RBRACE
  { PDecl_fun (make_fun_defn f false [] p r e $startpos $endpos) }
| FUN f=ident LT tvs=separated_list(COMMA, TVAR) GT
    LPAREN p=param_decls RPAREN ARROW r=type_expr EQ LBRACE e=expr RBRACE
  { PDecl_fun (make_fun_defn f false tvs p r e $startpos $endpos) }
| RECFUN f=ident LPAREN p=param_decls RPAREN ARROW r=type_expr EQ LBRACE e=expr RBRACE
  { PDecl_fun (make_fun_defn f true [] p r e $startpos $endpos) }
| RECFUN f=ident LT tvs=separated_list(COMMA, TVAR) GT
    LPAREN p=param_decls RPAREN ARROW r=type_expr EQ LBRACE e=expr RBRACE
  { PDecl_fun (make_fun_defn f true tvs p r e $startpos $endpos) }
| FORMAT LBRACE d=separated_list(SEMISEMI, format_decl) RBRACE
  { PDecl_format (make_format d $startpos $endpos) }

toplevel:
| pre_decls=list(pre_decl) EOF
  { { pre_decls } }
