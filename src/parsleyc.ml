open Lexing
open Location
open Ast
open AstToRustTranslator
open Pprint

let print_exception f loc msg =
  Printf.fprintf f "%s: %s\n" (Location.str_of_loc loc) msg

let process_ast ast =
  Type_check.type_check ast;
  (*(AstToRustTranslator.parse_ast ast)*)
  ()

let parse_file fname =
  let lexbuf = from_channel (open_in fname) in
  let lexbuf = { lexbuf with
                 lex_curr_p = { pos_fname = fname;
                                pos_lnum  = 1;
                                pos_bol   = 0;
                                pos_cnum  = 0 } } in
  try
    let ast = Parser.toplevel Lexer.token lexbuf in
    Pprint.print_ast Fmt.stdout ast;
    ()
  with
    | Parser.Error ->
          (Printf.fprintf stderr "%s: parser error at or just before this location\n"
                          (Location.str_of_curr_pos lexbuf);
           exit 1)
    | Failure f ->
          (let _bt = Printexc.get_backtrace () in
           Printf.fprintf stderr "%s: invalid token at or just before this location\n"
                          (Location.str_of_curr_pos lexbuf);
           (* Printf.fprintf stderr " %s\n" _bt; *)
           exit 1)
    | Lexer.Error (e, l) ->
          (print_exception stderr l (Lexer.error_string e);
           exit 1)
    | Parseerror.Error (e, l) ->
          (print_exception stderr l (Parseerror.error_string e);
           exit 1)
    | Type_check.Error (e, l) ->
          (print_exception stderr l (Type_check.error_string e);
           exit 1)

let () =
  parse_file Sys.argv.(1)
