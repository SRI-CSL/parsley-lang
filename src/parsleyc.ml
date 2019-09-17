open Lexing
open Location
open Ast

let print_exception f loc msg =
  Printf.fprintf f "%a: %s\n" Location.print_loc loc msg

let parse_file fname =
  let lexbuf = from_channel (open_in fname) in
  let lexbuf = { lexbuf with
                 lex_curr_p = { pos_fname = fname;
                                pos_lnum  = 1;
                                pos_bol   = 0;
                                pos_cnum  = 0 } } in
  try
    let _ = Parser.format Lexer.token lexbuf in
    ()
  with
    | Parser.Error ->
          (Location.print_curr_pos stderr lexbuf;
           Printf.fprintf stderr " parser error at or just before this location\n";
           exit 1)
    | Failure f ->
          (let bt = Printexc.get_backtrace () in
           Location.print_curr_pos stderr lexbuf;
           Printf.fprintf stderr " failure at or just before this location\n";
           Printf.fprintf stderr " %s\n" bt;
           exit 1)
    | Lexer.Error (e, l) ->
          (print_exception stderr l (Lexer.error_string e);
           exit 1)
    | Parseerror.Error (e, l) ->
          (print_exception stderr l (Parseerror.error_string e);
           exit 1)

let () =
  parse_file Sys.argv.(1)
