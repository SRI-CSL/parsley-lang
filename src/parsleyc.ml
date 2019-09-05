open Lexing
open Location
open Ast

let parse_file fname =
  let lexbuf = from_channel (open_in fname) in
  let lexbuf = { lexbuf with
                 lex_curr_p = { pos_fname = fname;
                                pos_lnum  = 1;
                                pos_bol   = 0;
                                pos_cnum  = 0 } } in
  let _ = Parser.format Lexer.token lexbuf in
  ()

let () =
  parse_file Sys.argv.(1)
