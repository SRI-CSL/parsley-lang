let opt_print_ast = ref false
let input_file = ref []

let usage = Printf.sprintf
              "Usage: %s <options> <file.ply> " (Sys.argv.(0))

let options =
  Arg.align ([
        ( "-p",
          Arg.Set opt_print_ast,
          " print the parsed AST")
      ])

let () =
  Arg.parse options (fun s -> input_file := s :: !input_file) usage;
  if List.length !input_file > 1 || List.length !input_file = 0
  then (Printf.eprintf "Please specify a single input file.\n";
        exit 1);
  let flat_decls = Parse_spec.parse_spec (List.hd !input_file) in
  if !opt_print_ast then
    Ast_printer.print_flat_program flat_decls
