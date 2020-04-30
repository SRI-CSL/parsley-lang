%{
open Ast
open Parseerror
%}

%token EOF
%token FORMAT LIBRARY TYPE FUN NTERM USE AS OF CASE LET IN
%token EPSILON

%token LBRACE RBRACE LPAREN RPAREN LBRACK RBRACK LPARBAR RPARBAR
%token BAR COMMA COLON COLONEQ SEMICOLON SEMISEMI QUOTE DOT QUESTION ARROW
%token STAR PLUS MINUS DIV
%token LT GT LTEQ GTEQ EQ NEQ LAND LOR
%token MATCH COLONCOLON BACKSLASH EXCLAIM UNDERSCORE

%token<Ast.literal> LITERAL
%token<Ast.ident>   ID
%token<Ast.ident>   UID
%token<Ast.tvar>    TVAR

%token<string Location.loc> INT_LITERAL
%token<string Location.loc> RE_CHAR_CLASS

%token<string Location.loc * string Location.loc> CONSTR

%start<Ast.top_level> toplevel

(* operators are increasing precedence order. *)
%nonassoc IN
%right EXCLAIM
%left  LAND LOR
%left  LT GT LTEQ GTEQ EQ MATCH
%left  BAR
%right COLONCOLON
%left  STAR DIV QUESTION
%left  PLUS MINUS
%left  LPAREN LBRACK
%left  ARROW
%nonassoc UMINUS AS

%{
let parse_error e loc =
  raise (Error (e, loc))

let make_int_literal s =
  let s, loc = (Location.value s), (Location.loc s) in
  try  int_of_string s
  with _ -> parse_error (Invalid_integer s) loc

let make_type_expr ty b e =
  { type_expr = ty;
    type_expr_loc = Location.make_loc b e }

let make_type_rep tr b e =
  { type_rep = tr;
    type_rep_loc = Location.make_loc b e }

let make_param_decl id ty b e =
  Location.mk_loc_val (id, ty) (Location.make_loc b e)

let make_expr exp b e =
  { expr = exp;
    expr_loc = Location.make_loc b e }

let make_pattern pat b e =
  { pattern = pat;
    pattern_loc = Location.make_loc b e }

let make_stmt s b e =
  { stmt = s;
    stmt_loc = Location.make_loc b e }

let make_action sl b e =
  { action_stmts = sl;
    action_loc = Location.make_loc b e }

let make_char_class cc b e =
  { char_class = cc;
    char_class_loc = Location.make_loc b e }

let make_rule_elem re b e =
  { rule_elem = re;
    rule_elem_loc = Location.make_loc b e }

let make_rule t res b e =
  { rule_temps = t;
    rule_rhs = res;
    rule_loc = Location.make_loc b e }

let make_nt_defn n v inh syn r b e =
  { non_term_name = n;
    non_term_varname = v;
    non_term_inh_attrs = inh;
    non_term_syn_attrs = syn;
    non_term_rules = r;
    non_term_loc = Location.make_loc b e }

let make_type_defn n tvs bd b e =
  { type_defn_ident = n;
    type_defn_tvars = tvs;
    type_defn_body = bd;
    type_defn_loc = Location.make_loc b e }

let make_fun_defn n p t bd b e =
  { fun_defn_ident = n;
    fun_defn_params = p;
    fun_defn_res_type = t;
    fun_defn_body = bd;
    fun_defn_loc = Location.make_loc b e }

let make_use m i b e =
  { use_module = m;
    use_idents = i;
    use_loc = Location.make_loc b e }

let make_nterm_decl d b e =
  { nterms = d;
    nterms_loc = Location.make_loc b e }

let make_format_decl d b e =
  { format_decl = d;
    format_decl_loc = Location.make_loc b e }

let make_format name decls b e =
  { format_name = name;
    format_decls = decls;
    format_loc = Location.make_loc b e }
%}

%%

ident:
| i=ID
  { i }

path:
| p=separated_nonempty_list(DOT, ident)
  { p }
| u=UID DOT p=separated_nonempty_list(DOT, ident)
  { u :: p }

type_expr:
| tv=TVAR
  { make_type_expr (TE_tvar tv) $startpos $endpos }
| p=path
  { make_type_expr (TE_constr (p, [])) $startpos $endpos }
| LPAREN l=separated_list(COMMA, type_expr) RPAREN
  { make_type_expr (TE_tuple l) $startpos $endpos }
| LBRACK t=type_expr RBRACK
  { make_type_expr (TE_list t) $startpos $endpos }
| p=path LT l=separated_list(COMMA, type_expr) GT
  { make_type_expr (TE_constr (p, l)) $startpos $endpos }
| LBRACE r=param_decls RBRACE
  { make_type_expr (TE_record r) $startpos $endpos }

type_variant:
| i=UID
  { (i, []) }
| i=UID OF l=separated_list(STAR, type_expr)
  { (i, l) }

type_rep:
| e=type_expr
  { make_type_rep (TR_expr e) $startpos $endpos }
| l=separated_nonempty_list(BAR, type_variant)
  { make_type_rep (TR_variant l) $startpos $endpos }

param_decl:
| i=ident COLON t=type_expr
  { make_param_decl i t $startpos $endpos }

param_decls:
| l=separated_list(COMMA, param_decl)
  { l }

rec_field:
| i=ident COLON e=expr
  { (i, e) }

rec_fields:
| l=separated_list(COMMA, rec_field)
  { l }

expr:
| p=path
  { make_expr (E_path p) $startpos $endpos }
| i=INT_LITERAL
  { make_expr (E_int (make_int_literal i)) $startpos $endpos }
| l=LITERAL
  { make_expr (E_literal l) $startpos $endpos }
| LPAREN l=separated_list(COMMA, expr) RPAREN
  { make_expr (E_tuple l) $startpos $endpos }
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
| LBRACE r=rec_fields RBRACE
  { make_expr (E_record r) $startpos $endpos }
| l=expr LAND r=expr
  { make_expr (E_binop (Land, l, r)) $startpos $endpos }
| l=expr LOR r=expr
  { make_expr (E_binop (Lor, l, r)) $startpos $endpos }
| e=expr MATCH c=CONSTR
  { make_expr (E_match (e, [fst c], snd c)) $startpos $endpos }
| l=expr PLUS r=expr
  { make_expr (E_binop (Plus, l, r)) $startpos $endpos }
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
| l=expr COLONCOLON r=expr
  { make_expr (E_binop (Cons, l, r)) $startpos $endpos }
| e=expr AS nt=UID
  { make_expr (E_cast_type (e, [nt])) $startpos $endpos }
| e=expr AS c=CONSTR
  { make_expr (E_cast_variant (e, [fst c], snd c)) $startpos $endpos }
| e=expr ARROW p=path
  { make_expr (E_field (e, p)) $startpos $endpos }
| LPAREN CASE e=expr OF option(BAR) b=separated_list(BAR, branch) RPAREN
  { make_expr (E_case (e, b)) $startpos $endpos }
| LET p=pattern EQ e=expr IN b=expr
  { make_expr (E_let (p, e, b)) $startpos $endpos }

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
  { make_pattern (P_literal l) $startpos $endpos }
| ps=pattern_args
  { make_pattern (P_tuple ps) $startpos $endpos }

pattern_args:
| LPAREN ps=separated_list(COMMA, pattern) RPAREN
  { ps }

branch:
| p=pattern ARROW e=expr
  { (p, e) }

stmt:
| l=expr COLONEQ r=expr
  { make_stmt (S_assign (l, r)) $startpos $endpos }

action:
| sl=separated_list(SEMICOLON, stmt)
  { make_action sl $startpos $endpos }

char_class:
| c=RE_CHAR_CLASS
  { make_char_class (CC_named c) $startpos $endpos }
| l=LITERAL
  { make_char_class (CC_literal l) $startpos $endpos }
| DOT
  { make_char_class CC_wildcard $startpos $endpos }
| l=char_class BAR r=LITERAL
  { make_char_class (CC_add (l, r)) $startpos $endpos }
| l=char_class BACKSLASH r=LITERAL
  { make_char_class (CC_sub (l, r)) $startpos $endpos }

attr_val:
| i=ident EQ v=expr
  { (i, v) }

nt_args:
| LT inh=separated_list(COMMA, attr_val) GT
  { inh }

cc_regex:
| c=char_class
  { make_rule_elem (RE_char_class c) $startpos $endpos }
| c=cc_regex STAR
  { make_rule_elem (RE_star c) $startpos $endpos }
| c=cc_regex PLUS
  { make_rule_elem (RE_plus c) $startpos $endpos }
| c=cc_regex QUESTION
  { make_rule_elem (RE_opt c) $startpos $endpos }
| LPAREN l=list(cc_regex) RPAREN
  { make_rule_elem (RE_seq l) $startpos $endpos }
| LBRACK c=char_class STAR e=expr RBRACK
  { make_rule_elem (RE_cclass_repeat (c, e)) $startpos $endpos }
| LBRACK nt=UID inh=option(nt_args) STAR e=expr RBRACK
  { make_rule_elem (RE_nterm_repeat (nt, inh, e)) $startpos $endpos }

rule_elem:
| EPSILON
  { make_rule_elem RE_epsilon $startpos $endpos }
| c=RE_CHAR_CLASS
  { let cc = make_char_class (CC_named c) $startpos $endpos in
    make_rule_elem (RE_char_class cc) $startpos $endpos }
| l=LITERAL
  { make_rule_elem (RE_literal l) $startpos $endpos }
| v=ident EQ nt=UID inh=option(nt_args)
  { make_rule_elem (RE_non_term (nt, Some v, inh)) $startpos $endpos }
| v=ident EQ LPAREN re=cc_regex RPAREN
  { make_rule_elem (RE_regex (re, Some(v))) $startpos $endpos }
| nt=UID inh=option(nt_args)
  { make_rule_elem (RE_non_term (nt, None, inh)) $startpos $endpos }
| LBRACK e=expr RBRACK
  { make_rule_elem (RE_constraint e) $startpos $endpos }
| LBRACE a=action RBRACE
  { make_rule_elem (RE_action a) $startpos $endpos }
| l=rule_elem BAR r=rule_elem
  { make_rule_elem (RE_choice (l, r)) $startpos $endpos }
| LPAREN l=list(rule_elem) RPAREN
  { make_rule_elem (RE_seq l) $startpos $endpos }
| e=rule_elem STAR
  { make_rule_elem (RE_star e) $startpos $endpos }
| e=rule_elem PLUS
  { make_rule_elem (RE_plus e) $startpos $endpos }
| e=rule_elem QUESTION
  { make_rule_elem (RE_opt e) $startpos $endpos }

rule:
| LPARBAR d=param_decls RPARBAR l=list(rule_elem)
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
  { make_nt_defn n v (ALT_decls []) (ALT_decls []) r $startpos $endpos }
| n=UID v=option(ident)
  LBRACE syn=nt_param_decls RBRACE COLONEQ
  r=separated_nonempty_list(SEMICOLON, rule)
  { make_nt_defn n v (ALT_decls []) syn r $startpos $endpos }
| n=UID v=option(ident)
  LPAREN inh=nt_param_decls RPAREN COLONEQ
  r=separated_nonempty_list(SEMICOLON, rule)
  { make_nt_defn n v inh (ALT_decls []) r $startpos $endpos }
| n=UID v=option(ident)
  LPAREN inh=nt_param_decls RPAREN
  LBRACE syn=nt_param_decls RBRACE COLONEQ
  r=separated_nonempty_list(SEMICOLON, rule)
  { make_nt_defn n v inh syn r $startpos $endpos }

format_decl:
| d=nt_defn
  { make_format_decl (Format_decl_non_term d) $startpos $endpos }

use_def:
| d=UID
| d=ident
  { d }

top_decl:
| USE m=ident COLON LBRACE i=separated_list(COMMA, use_def) RBRACE
  { Decl_use (make_use m i $startpos $endpos) }
| TYPE t=ident EQ e=type_rep
  { Decl_type (make_type_defn t [] e $startpos $endpos) }
| TYPE t=ident LPAREN tvs=separated_list(COMMA, TVAR) RPAREN EQ e=type_rep
  { Decl_type (make_type_defn t tvs e $startpos $endpos) }
| FUN f=ident LPAREN p=param_decls RPAREN ARROW r=type_expr EQ LBRACE e=expr RBRACE
  { Decl_fun (make_fun_defn f p r e $startpos $endpos) }
| NTERM LBRACE d=separated_list(COMMA, UID) RBRACE
  { Decl_nterm (make_nterm_decl d $startpos $endpos) }
| FORMAT i=UID LBRACE d=separated_list(SEMISEMI, format_decl) RBRACE
  { Decl_format (make_format i d $startpos $endpos) }

toplevel:
| decls=list(top_decl) EOF
  { { decls } }
