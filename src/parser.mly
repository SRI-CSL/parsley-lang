%{
open Location
open Ast
%}

%token FORMAT TYPE USE

%token LBRACE RBRACE LPAREN RPAREN LBRACK RBRACK LPARBAR RPARBAR
%token BAR COMMA COLON COLONEQ SEMICOLON QUOTE DOT QUESTION
%token STAR PLUS MINUS DIV
%token LT GT LTEQ GTEQ EQ NEQ LAND LOR
%token MATCH

%token <string Location.loc> LITERAL
%token <string Location.loc> ID
%token <string Location.loc> INT_LITERAL

%start <Ast.format> format

(* operators are increasing precedence order. *)
%left LT GT LTEQ GTEQ
%left BAR
%left STAR DIV QUESTION
%left PLUS MINUS
%left LPAREN LBRACK

%{

let make_int_literal s =
  (* TODO: handle exceptions *)
  int_of_string (Location.value s)

let make_type_expr ty b e =
  { type_expr = ty;
    type_expr_loc = make_loc b e }

let make_param_decl id ty b e =
  mk_loc_val (id, ty) (make_loc b e)

let make_expr exp b e =
  { expr = exp;
    expr_loc = make_loc b e }

let make_stmt s b e =
  { stmt = s;
    stmt_loc = make_loc b e }

let make_action sl b e =
  { action_stmts = sl;
    action_loc = make_loc b e }

let make_rule_elem re b e =
  { rule_elem = re;
    rule_elem_loc = make_loc b e }

let make_rule t res b e =
  { rule_temps = t;
    rule_rhs = res;
    rule_loc = make_loc b e }

let make_nt_defn n v d r b e =
  { non_term_name = n;
    non_term_varname = v;
    non_term_attrs = d;
    non_term_rules = r;
    non_term_loc = make_loc b e }

let make_use m i b e =
  { use_module = m;
    use_idents = i;
    use_loc = make_loc b e }

let make_decl d b e =
  { decl = d;
    decl_loc = make_loc b e }

let check_format_params params param_decls =
  (* TODO *)
  ()
let make_format name params param_decls decls b e =
  check_format_params params param_decls;
  { format_name = name;
    format_param_decls = param_decls;
    format_decls = decls;
    format_loc = make_loc b e;
  }

%}

%%

ident:
| i=ID
  { i }

type_expr:
| i=ident
  { make_type_expr (TE_id i) $startpos $endpos }
| LPAREN l=separated_list(COMMA, type_expr) RPAREN
  { make_type_expr (TE_tuple l) $startpos $endpos }
| LBRACK t=type_expr RBRACK
  { make_type_expr (TE_list t) $startpos $endpos }
| i=ident LT l=separated_list(COMMA, type_expr) GT
  { make_type_expr (TE_constr (i, l)) $startpos $endpos }

param_decl:
| i=ident COLON t=type_expr
  { make_param_decl i t $startpos $endpos }

param_decls:
| l=separated_list(COMMA, param_decl)
  { l }

expr:
| p=separated_nonempty_list(DOT, ident)
  { make_expr (E_path p) $startpos $endpos }
| i=INT_LITERAL
  { make_expr (E_int (make_int_literal i)) $startpos $endpos }
| LPAREN l=separated_list(COMMA, expr) RPAREN
  { make_expr (E_tuple l) $startpos $endpos }
| e=expr LPAREN l=separated_list(COMMA, expr) RPAREN
  { make_expr (E_apply(e, l)) $startpos $endpos }
| e=expr LBRACK i=expr RBRACK
  { make_expr (E_index(e, i)) $startpos $endpos }

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

stmt:
| l=expr COLONEQ r=expr
  { make_stmt (S_assign (l, r)) $startpos $endpos }

action:
| sl=separated_list(SEMICOLON, stmt)
  { make_action sl $startpos $endpos }

rule_elem:
| l=LITERAL
  { make_rule_elem (RE_literal l) $startpos $endpos }
| v=ident EQ nt=ident
  { make_rule_elem (RE_non_term (nt, Some v)) $startpos $endpos }
| nt=ident
  { make_rule_elem (RE_non_term (nt, None)) $startpos $endpos }
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
| LPARBAR d=param_decls RPARBAR l=list(rule_elem) SEMICOLON
  { make_rule d l $startpos $endpos }
| l=list(rule_elem) SEMICOLON
  { make_rule [] l $startpos $endpos }

nt_defn:
| n=ident v=option(ident) LBRACE d=param_decls RBRACE r=list(rule)
  { make_nt_defn n v d r $startpos $endpos }

use:
| USE m=ident COLON LBRACE i=separated_list(COMMA, ident) RBRACE
  { make_use m i $startpos $endpos }

decl:
| d=nt_defn
  { make_decl (Decl_non_term d) $startpos $endpos }
| u=use
  { make_decl (Decl_use u) $startpos $endpos }
| TYPE t=ident EQ e=type_expr
  { make_decl (Decl_type (t, e)) $startpos $endpos }

format:
| FORMAT i=ident LBRACE d=separated_list(DOT, decl) RBRACE
  { make_format i [] [] d $startpos $endpos }
| FORMAT i=ident
    LPAREN ps=separated_list(COMMA, ident) RPAREN
    pds=separated_list(COMMA, param_decl)
    LBRACE d=separated_list(DOT, decl) RBRACE
  { make_format i ps pds d $startpos $endpos }
