open Lexing
open Location
open Ast

let opt_do_type_check = ref true
let input_files = ref []

let print_exception f loc msg =
  Printf.fprintf f "%s: %s\n" (Location.str_of_loc loc) msg

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

let options = Arg.align ([
                    ( "-no-tc",
                      Arg.Clear opt_do_type_check,
                      " disable type checking" );
                ])

let usage = Printf.sprintf
              "Usage: %s <options> <file.ply> <file.ply> ..." (Sys.argv.(0))

let () =
  Arg.parse options (fun s -> input_files := (!input_files) @ [s]) usage;
  if List.length !input_files = 0
  then Printf.eprintf "%s\n" usage
  else List.iter parse_file !input_files
