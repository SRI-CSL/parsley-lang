open TypingEnvironment
open TypeInfer
let opt_print_ast = ref false
let opt_type_check = ref true
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
  let spec = SpecParser.parse_spec (List.hd !input_file) in
  if !opt_print_ast then
    AstPrinter.print_program spec;
  if !opt_type_check then
    SpecTyper.type_check spec
