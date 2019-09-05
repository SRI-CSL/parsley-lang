{
  open Lexing
  open Parser

  type error =
    | Unterminated_string

  exception Error of error * position

  let token_buf = ref (Buffer.create 256)

  (* keywords *)
  let keywords =
    [ "format", FORMAT;
      "use", USE;
      "type", TYPE;
    ]

  let reset_token_buffer () =
    Buffer.clear !token_buf

  let get_stored_token () =
    Buffer.contents !token_buf

  let store_token lexbuf =
    Buffer.add_string !token_buf (Lexing.lexeme lexbuf)

  let store_char c =
    Buffer.add_char !token_buf c
}

let newline = ('\013'* '\010')
let blank = [' ' '\009' '\012']
let alpha = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let alnum = ['A'-'Z' 'a'-'z' '0'-'9']

let ident = ['A'-'Z' 'a'-'z' '0'-'9' '_' '@']
let int_literal = '-'? ['0'-'9']+

rule token = parse
| newline
    { newline lexbuf;
      token lexbuf }
| blank +
    { token lexbuf }
| "//"
    { eol_comment lexbuf }
| "'"
    { reset_token_buffer ();
      quote lexbuf;
      let t = get_stored_token () in
      reset_token_buffer ();
      let t = Location.mk_loc_val t (Location.curr lexbuf) in
      LITERAL t
    }
| "|"  { BAR }
| "{"  { LBRACE }
| "}"  { RBRACE }
| "("  { LPAREN }
| ")"  { RPAREN }
| "["  { LBRACK }
| "]"  { RBRACK }
| "(|" { LPARBAR }
| "|)" { RPARBAR }
| "."  { DOT }
| ","  { COMMA }
| ";"  { SEMICOLON}
| ":=" { COLONEQ }
| ":"  { COLON }
| "+"  { PLUS }
| "-"  { MINUS }
| "*"  { STAR }
| "/"  { DIV }
| "&&" { LAND }
| "||" { LOR }
| "<"  { LT }
| ">"  { GT }
| "<=" { LTEQ }
| ">=" { GTEQ }
| "!=" { NEQ }
| "="  { EQ }
| "~~" { MATCH }
| "?"  { QUESTION }

| "$"? alpha ident+
    { let s = Lexeme.lexeme lexbuf in
      ID (Location.mk_loc_val s (Location.curr lexbuf)) }
| int_literal
    { let s = Lexeme.lexeme lexbuf in
      INT_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

and eol_comment = parse
| newline
    { newline lexbuf;
      token lexbuf }
| _
    { eol_comment lexbuf }

and quote = parse
| "'"
    { store_lexeme lexbuf }
| newline
    { newline lexbuf;
      quote lexbuf }
| _
    { quote lexbuf }
