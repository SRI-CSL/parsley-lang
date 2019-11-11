{
  open Lexing
  open Parser

  type error =
    | Unterminated_string

  exception Error of error * Location.t

  let error_string = function
    | Unterminated_string ->
          "unterminated string"

  let token_buf = ref (Buffer.create 256)

  let keywords =
    let tbl = Hashtbl.create 16 in
    List.iter (fun (key, tok) -> Hashtbl.add tbl key tok)
              [ "format", FORMAT;
                "use",    USE;
                "type",   TYPE;
                "fun",    FUN;
                "as",     AS;
                "of",     OF;
                "case",   CASE;
                "let",    LET;
                "in",     IN;

                "$typeof",  TYPEOF;
                "$epsilon", EPSILON;
              ];
    tbl

  let decide_ident s loc =
    match (Hashtbl.find_opt keywords s) with
      | Some tok -> tok
      | None     -> ID (Location.mk_loc_val s loc)

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
let upper = ['A'-'Z']
let alpha = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let alnum = ['A'-'Z' 'a'-'z' '0'-'9']

let ident = ['A'-'Z' 'a'-'z' '0'-'9' '_' '@']
let int_literal = '-'? ['0'-'9']+

let re_char_class = "[:" alnum+ ":]"

rule token = parse
| newline
    { new_line lexbuf;
      token lexbuf }
| blank +
    { token lexbuf }
| "//"
    { eol_comment lexbuf }
| "\""
    { reset_token_buffer ();
      quote lexbuf;
      let t = get_stored_token () in
      reset_token_buffer ();
      let t = Location.mk_loc_val t (Location.curr lexbuf) in
      LITERAL t
    }
| "(|" { LPARBAR }
| "|)" { RPARBAR }
| "|"  { BAR }
| "{"  { LBRACE }
| "}"  { RBRACE }
| "("  { LPAREN }
| ")"  { RPAREN }
| "["  { LBRACK }
| "]"  { RBRACK }
| "."  { DOT }
| "_"  { UNDERSCORE }
| ","  { COMMA }
| ":=" { COLONEQ }
| "::" { COLONCOLON }
| ":"  { COLON }
| ";;" { SEMISEMI }
| ";"  { SEMICOLON}
| "+"  { PLUS }
| "->" { ARROW }
| "-"  { MINUS }
| "*"  { STAR }
| "/"  { DIV }
| "&&" { LAND }
| "||" { LOR }
| "<=" { LTEQ }
| ">=" { GTEQ }
| "!=" { NEQ }
| "!"  { EXCLAIM }
| "<"  { LT }
| ">"  { GT }
| "="  { EQ }
| "~~" { MATCH }
| "?"  { QUESTION }
| "\\" { BACKSLASH }

| upper ident*
    { let id = Lexing.lexeme lexbuf in
      UID (Location.mk_loc_val id (Location.curr lexbuf)) }
| "$"? alpha ident*
    { decide_ident (Lexing.lexeme lexbuf) (Location.curr lexbuf) }

| "'" alpha ident*
    { let tv = Lexing.lexeme lexbuf in
      TVAR (Location.mk_loc_val tv (Location.curr lexbuf)) }

| int_literal
    { let s = Lexing.lexeme lexbuf in
      INT_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| re_char_class
    { let s = Lexing.lexeme lexbuf in
      RE_CHAR_CLASS (Location.mk_loc_val s (Location.curr lexbuf)) }

| eof
    { EOF }

and eol_comment = parse
| newline
    { new_line lexbuf;
      token lexbuf }
| _
    { eol_comment lexbuf }

and quote = parse
| "\""
    { () }

| newline
    { store_token lexbuf;
      new_line lexbuf;
      quote lexbuf }
| _
    { store_token lexbuf;
      quote lexbuf }
