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

  let token_buf = ref (Buffer.create 256)

  let keywords =
    let tbl = Hashtbl.create 16 in
    List.iter (fun (key, tok) -> Hashtbl.add tbl key tok)
      [ "format",    FORMAT;
        "bitfield",  BITFIELD;
        "include",   INCLUDE;
        "import",    IMPORT;
        "type",      TYPE;
        "and",       AND;
        "fun",       FUN;
        "recfun",    RECFUN;
        "of",        OF;
        "case",      CASE;
        "let",       LET;
        "in",        IN;
        "const",     CONST;
        "foreign",   FOREIGN;

        "$epsilon",  EPSILON;
        "$pad",      PAD;
        "$align",    ALIGN;
        "$bitfield", USE_BITFIELD;
        "$print",    PRINT;
        "$print_t",  PRINTT;
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
let int_suffix  = '_' ('i'|'u') ("8"|"16"|"32"|"64")

let re_char_class = "[:" alnum+ ":]"

rule token = parse
| newline
    { new_line lexbuf;
      token lexbuf }
| blank +
    { token lexbuf }

| "/sf[" { SLASH_SF_LBRACK }
| "/sb[" { SLASH_SB_LBRACK }

| "|_b" { BAR_B }
| "&_b" { AND_B }
| "+_s" { PLUS_S }
| "@#[" { AT_MAP }
| "@^[" { SET_VIEW }

| "+_i"    { PLUS  (S_signed, NW_size) }
| "-_i"    { MINUS (S_signed, NW_size) }
| "*_i"    { MUL   (S_signed, NW_size) }
| "/_i"    { DIV   (S_signed, NW_size) }
| "%_i"    { MOD   (S_signed, NW_size) }
| "<_i"    { LT    (S_signed, NW_size) }
| ">_i"    { GT    (S_signed, NW_size) }
| "<=_i"   { LTEQ  (S_signed, NW_size) }
| ">=_i"   { GTEQ  (S_signed, NW_size) }
| "~_i"    { IB_NOT(S_signed, NW_size) }
| "&_i"    { IB_AND(S_signed, NW_size) }
| "|_i"    { IB_OR (S_signed, NW_size) }
| "^_i"    { IB_XOR(S_signed, NW_size) }
| "<<_i"   { LSHFT (S_signed, NW_size) }
| ">>_i"   { RSHFT (S_signed, NW_size) }
| ">>_ai"  { ASHFT (S_signed, NW_size) }

| "+_i8"   { PLUS  (S_signed, NW_8) }
| "-_i8"   { MINUS (S_signed, NW_8) }
| "*_i8"   { MUL   (S_signed, NW_8) }
| "/_i8"   { DIV   (S_signed, NW_8) }
| "%_i8"   { MOD   (S_signed, NW_8) }
| "<_i8"   { LT    (S_signed, NW_8) }
| ">_i8"   { GT    (S_signed, NW_8) }
| "<=_i8"  { LTEQ  (S_signed, NW_8) }
| ">=_i8"  { GTEQ  (S_signed, NW_8) }
| "~_i8"   { IB_NOT(S_signed, NW_8) }
| "&_i8"   { IB_AND(S_signed, NW_8) }
| "|_i8"   { IB_OR (S_signed, NW_8) }
| "^_i8"   { IB_XOR(S_signed, NW_8) }
| "<<_i8"  { LSHFT (S_signed, NW_8) }
| ">>_i8"  { RSHFT (S_signed, NW_8) }
| ">>_ai8" { ASHFT (S_signed, NW_8) }

| "+_i16"  { PLUS  (S_signed, NW_16) }
| "-_i16"  { MINUS (S_signed, NW_16) }
| "*_i16"  { MUL   (S_signed, NW_16) }
| "/_i16"  { DIV   (S_signed, NW_16) }
| "%_i16"  { MOD   (S_signed, NW_16) }
| "<_i16"  { LT    (S_signed, NW_16) }
| ">_i16"  { GT    (S_signed, NW_16) }
| "<=_i16" { LTEQ  (S_signed, NW_16) }
| ">=_i16" { GTEQ  (S_signed, NW_16) }
| "~_i16"  { IB_NOT(S_signed, NW_16) }
| "&_i16"  { IB_AND(S_signed, NW_16) }
| "|_i16"  { IB_OR (S_signed, NW_16) }
| "^_i16"  { IB_XOR(S_signed, NW_16) }
| "<<_i16" { LSHFT (S_signed, NW_16) }
| ">>_i16" { RSHFT (S_signed, NW_16) }
| ">>_ai16"{ ASHFT (S_signed, NW_16) }

| "+_i32"  { PLUS  (S_signed, NW_32) }
| "-_i32"  { MINUS (S_signed, NW_32) }
| "*_i32"  { MUL   (S_signed, NW_32) }
| "/_i32"  { DIV   (S_signed, NW_32) }
| "%_i32"  { MOD   (S_signed, NW_32) }
| "<_i32"  { LT    (S_signed, NW_32) }
| ">_i32"  { GT    (S_signed, NW_32) }
| "<=_i32" { LTEQ  (S_signed, NW_32) }
| ">=_i32" { GTEQ  (S_signed, NW_32) }
| "~_i32"  { IB_NOT(S_signed, NW_32) }
| "&_i32"  { IB_AND(S_signed, NW_32) }
| "|_i32"  { IB_OR (S_signed, NW_32) }
| "^_i32"  { IB_XOR(S_signed, NW_32) }
| "<<_i32" { LSHFT (S_signed, NW_32) }
| ">>_i32" { RSHFT (S_signed, NW_32) }
| ">>_ai32"{ ASHFT (S_signed, NW_32) }

| "+_i64"  { PLUS  (S_signed, NW_64) }
| "-_i64"  { MINUS (S_signed, NW_64) }
| "*_i64"  { MUL   (S_signed, NW_64) }
| "/_i64"  { DIV   (S_signed, NW_64) }
| "%_i64"  { MOD   (S_signed, NW_64) }
| "<_i64"  { LT    (S_signed, NW_64) }
| ">_i64"  { GT    (S_signed, NW_64) }
| "<=_i64" { LTEQ  (S_signed, NW_64) }
| ">=_i64" { GTEQ  (S_signed, NW_64) }
| "~_i64"  { IB_NOT(S_signed, NW_64) }
| "&_i64"  { IB_AND(S_signed, NW_64) }
| "|_i64"  { IB_OR (S_signed, NW_64) }
| "^_i64"  { IB_XOR(S_signed, NW_64) }
| "<<_i64" { LSHFT (S_signed, NW_64) }
| ">>_i64" { RSHFT (S_signed, NW_64) }
| ">>_ai64"{ ASHFT (S_signed, NW_64) }

| "+_u"    { PLUS  (S_unsigned, NW_size) }
| "-_u"    { MINUS (S_unsigned, NW_size) }
| "*_u"    { MUL   (S_unsigned, NW_size) }
| "/_u"    { DIV   (S_unsigned, NW_size) }
| "%_u"    { MOD   (S_unsigned, NW_size) }
| "<_u"    { LT    (S_unsigned, NW_size) }
| ">_u"    { GT    (S_unsigned, NW_size) }
| "<=_u"   { LTEQ  (S_unsigned, NW_size) }
| ">=_u"   { GTEQ  (S_unsigned, NW_size) }
| "~_u"    { IB_NOT(S_unsigned, NW_size) }
| "&_u"    { IB_AND(S_unsigned, NW_size) }
| "|_u"    { IB_OR (S_unsigned, NW_size) }
| "^_u"    { IB_XOR(S_unsigned, NW_size) }
| "<<_u"   { LSHFT (S_unsigned, NW_size) }
| ">>_u"   { RSHFT (S_unsigned, NW_size) }
| ">>_au"  { ASHFT (S_unsigned, NW_size) }

| "+_u8"   { PLUS  (S_unsigned, NW_8) }
| "-_u8"   { MINUS (S_unsigned, NW_8) }
| "*_u8"   { MUL   (S_unsigned, NW_8) }
| "/_u8"   { DIV   (S_unsigned, NW_8) }
| "%_u8"   { MOD   (S_unsigned, NW_8) }
| "<_u8"   { LT    (S_unsigned, NW_8) }
| ">_u8"   { GT    (S_unsigned, NW_8) }
| "<=_u8"  { LTEQ  (S_unsigned, NW_8) }
| ">=_u8"  { GTEQ  (S_unsigned, NW_8) }
| "~_u8"   { IB_NOT(S_unsigned, NW_8) }
| "&_u8"   { IB_AND(S_unsigned, NW_8) }
| "|_u8"   { IB_OR (S_unsigned, NW_8) }
| "^_u8"   { IB_XOR(S_unsigned, NW_8) }
| "<<_u8"  { LSHFT (S_unsigned, NW_8) }
| ">>_u8"  { RSHFT (S_unsigned, NW_8) }
| ">>_au8" { ASHFT (S_unsigned, NW_8) }

| "+_u16"  { PLUS  (S_unsigned, NW_16) }
| "-_u16"  { MINUS (S_unsigned, NW_16) }
| "*_u16"  { MUL   (S_unsigned, NW_16) }
| "/_u16"  { DIV   (S_unsigned, NW_16) }
| "%_u16"  { MOD   (S_unsigned, NW_16) }
| "<_u16"  { LT    (S_unsigned, NW_16) }
| ">_u16"  { GT    (S_unsigned, NW_16) }
| "<=_u16" { LTEQ  (S_unsigned, NW_16) }
| ">=_u16" { GTEQ  (S_unsigned, NW_16) }
| "~_u16"  { IB_NOT(S_unsigned, NW_16) }
| "&_u16"  { IB_AND(S_unsigned, NW_16) }
| "|_u16"  { IB_OR (S_unsigned, NW_16) }
| "^_u16"  { IB_XOR(S_unsigned, NW_16) }
| "<<_u16" { LSHFT (S_unsigned, NW_16) }
| ">>_u16" { RSHFT (S_unsigned, NW_16) }
| ">>_au16"{ ASHFT (S_unsigned, NW_16) }

| "+_u32"  { PLUS  (S_unsigned, NW_32) }
| "-_u32"  { MINUS (S_unsigned, NW_32) }
| "*_u32"  { MUL   (S_unsigned, NW_32) }
| "/_u32"  { DIV   (S_unsigned, NW_32) }
| "%_u32"  { MOD   (S_unsigned, NW_32) }
| "<_u32"  { LT    (S_unsigned, NW_32) }
| ">_u32"  { GT    (S_unsigned, NW_32) }
| "<=_u32" { LTEQ  (S_unsigned, NW_32) }
| ">=_u32" { GTEQ  (S_unsigned, NW_32) }
| "~_u32"  { IB_NOT(S_unsigned, NW_32) }
| "&_u32"  { IB_AND(S_unsigned, NW_32) }
| "|_u32"  { IB_OR (S_unsigned, NW_32) }
| "^_u32"  { IB_XOR(S_unsigned, NW_32) }
| "<<_u32" { LSHFT (S_unsigned, NW_32) }
| ">>_u32" { RSHFT (S_unsigned, NW_32) }
| ">>_au32"{ ASHFT (S_unsigned, NW_32) }

| "+_u64"  { PLUS  (S_unsigned, NW_64) }
| "-_u64"  { MINUS (S_unsigned, NW_64) }
| "*_u64"  { MUL   (S_unsigned, NW_64) }
| "/_u64"  { DIV   (S_unsigned, NW_64) }
| "%_u64"  { MOD   (S_unsigned, NW_64) }
| "<_u64"  { LT    (S_unsigned, NW_64) }
| ">_u64"  { GT    (S_unsigned, NW_64) }
| "<=_u64" { LTEQ  (S_unsigned, NW_64) }
| ">=_u64" { GTEQ  (S_unsigned, NW_64) }
| "~_u64"  { IB_NOT(S_unsigned, NW_64) }
| "&_u64"  { IB_AND(S_unsigned, NW_64) }
| "|_u64"  { IB_OR (S_unsigned, NW_64) }
| "^_u64"  { IB_XOR(S_unsigned, NW_64) }
| "<<_u64" { LSHFT (S_unsigned, NW_64) }
| ">>_u64" { RSHFT (S_unsigned, NW_64) }
| ">>_au64"{ ASHFT (S_unsigned, NW_64) }

| "//" { eol_comment lexbuf }

| "#[" { DECO }
| "(#" { SYN_BEGIN }
| "#)" { SYN_END }
| "@(" { AT_POS }
| "@[" { AT_VIEW }
| "(|" { LPARBAR }
| "|)" { RPARBAR }
| "[[" { LLBRACK }
| "]]" { RRBRACK }
| "[]" { LBRACKRBRACK }
| ":=" { COLONEQ }
| "::" { COLONCOLON }
| ";;" { SEMISEMI }
| "<-" { LARROW }
| "->" { ARROW }
| "&&" { LAND }
| "||" { LOR }
| "!=" { NEQ }
| "~~" { CONSTR_MATCH }
| ".." { DOTDOT }

| "\"" { reset_token_buffer ();
         quote lexbuf;
         let t = get_stored_token () in
         reset_token_buffer ();
         let t = Location.mk_loc_val t (Location.curr lexbuf) in
         LITERAL t }
| "\\" { BACKSLASH }
| "@"  { AT }
| "|"  { BAR }
| "{"  { LBRACE }
| "}"  { RBRACE }
| "("  { LPAREN }
| ")"  { RPAREN }
| "["  { LBRACK }
| "]"  { RBRACK }
| "."  { DOT }
| ","  { COMMA }
| ":"  { COLON }
| ";"  { SEMICOLON}
| "~"  { TILDE }
| "!"  { EXCLAIM }
| "="  { EQ }
| "?"  { QUESTION }
| "^"  { CARET }
| "#"  { HASH }
| "*"  { STAR }
| "+"  { POS }
| "-"  { NEG }
| "<"  { LANGLE }
| ">"  { RANGLE }

| upper ident*
    { let id = Lexing.lexeme lexbuf in
      UID (Location.mk_loc_val id (Location.curr lexbuf)) }
| lower ident* "::" upper ident*
    { let id = Lexing.lexeme lexbuf in
      let ls = String.split_on_char ':' id in
      let c, v = List.hd ls, List.nth ls 2 in
      let c = Location.mk_loc_val c (Location.curr lexbuf) in
      let v = Location.mk_loc_val v (Location.curr lexbuf) in
      CONSTR (None, c, v) }
| upper ident* "." lower ident* "::" upper ident*
    { let id = Lexing.lexeme lexbuf in
      let ls = String.split_on_char ':' id in
      let c, v = List.hd ls, List.nth ls 2 in
      let ls = String.split_on_char '.' c in
      let m, c = List.hd ls, List.nth ls 1 in
      let m = Location.mk_loc_val m (Location.curr lexbuf) in
      let c = Location.mk_loc_val c (Location.curr lexbuf) in
      let v = Location.mk_loc_val v (Location.curr lexbuf) in
      CONSTR (Some m, c, v) }

| "$"? "_"* alpha ident*
    { decide_ident (Lexing.lexeme lexbuf) (Location.curr lexbuf) }

| "'" alpha ident*
    { let tv = Lexing.lexeme lexbuf in
      TVAR (Location.mk_loc_val tv (Location.curr lexbuf)) }

| "0b" bit+
    { let s = Lexing.lexeme lexbuf in
      BV_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| (int_literal as i) '_'? "i8"
    { let s = i, Ast.i8_t in
      INT_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| (int_literal as i) '_'? "i16"
    { let s = i, Ast.i16_t in
      INT_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| (int_literal as i) '_'? "i32"
    { let s = i, Ast.i32_t in
      INT_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| (int_literal as i) '_'? "i64"
    { let s = i, Ast.i64_t in
      INT_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| (int_literal as i) '_'? "u8"
    { let s = i, Ast.u8_t in
      INT_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| (int_literal as i) '_'? "u16"
    { let s = i, Ast.u16_t in
      INT_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| (int_literal as i) '_'? "u32"
    { let s = i, Ast.u32_t in
      INT_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| (int_literal as i) '_'? "u64"
    { let s = i, Ast.u64_t in
      INT_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| (int_literal as i) '_'? "i"
    { let s = i, Ast.isize_t in
      INT_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| (int_literal as i) '_'? "u"
    { let s = i, Ast.usize_t in
      INT_LITERAL (Location.mk_loc_val s (Location.curr lexbuf)) }

| (int_literal as i)
    { RAW_INT (Location.mk_loc_val i (Location.curr lexbuf)) }

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
