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

(* Portions adapted from the OCaml lexer.

   Copyright 1996 Institut National de Recherche en Informatique et
     en Automatique.
*)

{
  type error =
    | Illegal_backslash of Location.t
    | Unterminated_backslash of Location.t
    | Illegal_escape of Location.t * string * string

  exception Error of error

  let msg m loc =
      Printf.sprintf m (Location.str_of_loc loc)

  let error_msg = function
    | Illegal_backslash l ->
        msg "%s:\n Illegal backslash" l
    | Unterminated_backslash l ->
        msg "%s:\n Unterminated backslash" l
    | Illegal_escape (l, s, r) ->
        msg "%s:\n Illegal escape '%s': %s" l s r

  let illegal_escape lexbuf reason =
    let loc = Location.curr lexbuf in
    let err = Illegal_escape (loc, Lexing.lexeme lexbuf, reason) in
    raise (Error err)

  (* computing literal values *)

  let digit_value c =
    match c with
      | 'a' .. 'f' -> 10 + Char.code c - Char.code 'a'
      | 'A' .. 'F' -> 10 + Char.code c - Char.code 'A'
      | '0' .. '9' -> Char.code c - Char.code '0'
      | _ -> assert false

  let num_value lexbuf ~base ~first ~last =
    let c = ref 0 in
    for i = first to last do
      let v = digit_value (Lexing.lexeme_char lexbuf i) in
      assert(v < base);
      c := (base * !c) + v
    done;
    !c

  let char_for_backslash = function
    | 'n' -> '\010'
    | 'r' -> '\013'
    | 'b' -> '\008'
    | 't' -> '\009'
    | c   -> c

  let char_for_decimal_code lexbuf i =
    let c = num_value lexbuf ~base:10 ~first:i ~last:(i+2) in
    if (c < 0 || c > 255) then
      illegal_escape lexbuf
        (Printf.sprintf
           "%d is outside the range of legal characters (0-255)." c)
    else Char.chr c

  let char_for_octal_code lexbuf i =
    let c = num_value lexbuf ~base:8 ~first:i ~last:(i+2) in
    if (c < 0 || c > 255) then
      illegal_escape lexbuf
        (Printf.sprintf
           "o%o (=%d) is outside the range of legal characters (0-255)." c c)
    else Char.chr c

  let char_for_hexadecimal_code lexbuf i =
    Char.chr (num_value lexbuf ~base:16 ~first:i ~last:(i+1))

  (* management of the conversion buffer *)

  let literal_buf = Buffer.create 256

  let reset_literal () =
    Buffer.reset literal_buf

  let store_char c =
    Buffer.add_char literal_buf c

  let get_literal () =
    Buffer.contents literal_buf
}

(*
   The lexing rule below converts any escapes in the interior contents
   of regular expression literals (i.e. the contents without any
   outermost quotes) into their denoted characters.  It is called only
   on regular expression literals, so it is intentionally kept
   separate, and called explicitly and directly without going through
   the parser.
 *)

rule literal = parse
| '\\' (['\\' '\'' '\"' 'n' 't' 'b' 'r' ' '] as c)
    { store_char (char_for_backslash c);
      literal lexbuf }

| '\\' ['0'-'9'] ['0'-'9'] ['0'-'9']
    { store_char (char_for_decimal_code lexbuf 1);
      literal lexbuf }

| '\\' 'o' ['0'-'7'] ['0'-'7'] ['0'-'7']
    { store_char (char_for_octal_code lexbuf 2);
      literal lexbuf }

| '\\' 'x' ['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F']
    { store_char (char_for_hexadecimal_code lexbuf 2);
      literal lexbuf }

| '\\' _
    { let loc = Location.curr lexbuf in
      raise (Error (Illegal_backslash loc)) }

| '\\' eof
    { let loc = Location.curr lexbuf in
      raise (Error (Unterminated_backslash loc)) }

| (_ as c)
    { store_char c;
      literal lexbuf }

| eof
    { get_literal () }
