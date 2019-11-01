open Lexing
open Location
open Ast

let print_exception f loc msg =
  Printf.fprintf f "%a: %s\n" Location.print_loc loc msg

let process_ast ast =
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
    process_ast ast;
    ()
  with
    | Parser.Error ->
          (Location.print_curr_pos stderr lexbuf;
           Printf.fprintf stderr " parser error at or just before this location\n";
           exit 1)
    | Failure f ->
          (let _bt = Printexc.get_backtrace () in
           Location.print_curr_pos stderr lexbuf;
           Printf.fprintf stderr " invalid token at or just before this location\n";
           (* Printf.fprintf stderr " %s\n" _bt; *)
           exit 1)
    | Lexer.Error (e, l) ->
          (print_exception stderr l (Lexer.error_string e);
           exit 1)
    | Parseerror.Error (e, l) ->
          (print_exception stderr l (Parseerror.error_string e);
           exit 1)

let () =
  parse_file Sys.argv.(1)
