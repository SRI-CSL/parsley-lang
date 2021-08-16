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
      [ "format",   FORMAT;
        "bitfield", BITFIELD;
        "use",      USE;
        "type",     TYPE;
        "and",      AND;
        "fun",      FUN;
        "recfun",   RECFUN;
        "of",       OF;
        "case",     CASE;
        "let",      LET;
        "in",       IN;

        "$epsilon",  EPSILON;
        "$pad",      PAD;
        "$align",    ALIGN;
        "$bitfield", USE_BITFIELD;
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
let lower = ['a'-'z']
let upper = ['A'-'Z']
let alpha = ['A'-'Z' 'a'-'z']
let digit = ['0'-'9']
let alnum = ['A'-'Z' 'a'-'z' '0'-'9']
let bit   = ['0' '1']
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
| "|_b"  { BAR_B }
| "&_b"  { AND_B }
| "+_s"  { PLUS_S }
| "#[" { ATTR }
| "(#" { SYN_BEGIN }
| "#)" { SYN_END }
| "@(" { AT_POS }
| "@[" { AT_VIEW }
| "@#["{ AT_MAP }
| "@^["{ SET_VIEW }
| "@"  { AT }
| "(|" { LPARBAR }
| "|)" { RPARBAR }
| "[[" { LLBRACK }
| "]]" { RRBRACK }
| "[]" { LBRACKRBRACK }
| "|"  { BAR }
| "{"  { LBRACE }
| "}"  { RBRACE }
| "("  { LPAREN }
| ")"  { RPAREN }
| "["  { LBRACK }
| "]"  { RBRACK }
| "."  { DOT }
| ","  { COMMA }
| ":=" { COLONEQ }
| "::" { COLONCOLON }
| ":"  { COLON }
| ";;" { SEMISEMI }
| ";"  { SEMICOLON}
| "+"  { PLUS }
| "->" { ARROW }
| "~"  { TILDE }
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
| "~~" { CONSTR_MATCH }
| "?"  { QUESTION }
| "\\" { BACKSLASH }
| "^"  { CARET }
| "#"  { HASH }
| ".." { DOTDOT }

| upper ident*
    { let id = Lexing.lexeme lexbuf in
      UID (Location.mk_loc_val id (Location.curr lexbuf)) }
| lower ident* "::" upper ident*
    { let id = Lexing.lexeme lexbuf in
      let ls = String.split_on_char ':' id in
      let c, v = List.hd ls, List.nth ls 2 in
      let c = Location.mk_loc_val c (Location.curr lexbuf) in
      let v = Location.mk_loc_val v (Location.curr lexbuf) in
      CONSTR (c, v) }

| "$"? "_"* alpha ident*
    { decide_ident (Lexing.lexeme lexbuf) (Location.curr lexbuf) }

| "'" alpha ident*
    { let tv = Lexing.lexeme lexbuf in
      TVAR (Location.mk_loc_val tv (Location.curr lexbuf)) }

| "0b" bit+
    { let s = Lexing.lexeme lexbuf in
      BV_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| int_literal
    { let s = Lexing.lexeme lexbuf in
      INT_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| "_"  { UNDERSCORE }

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
