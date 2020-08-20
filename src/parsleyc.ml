let opt_do_type_check = ref true
let input_file = ref None

let options = Arg.align ([
                    ( "-no-tc",
                      Arg.Clear opt_do_type_check,
                      " disable type checking" );
                ])

let usage = Printf.sprintf
              "Usage: %s <options> <file.ply> " (Sys.argv.(0))

let () =
  Arg.parse options (fun s -> input_file := Some s) usage;
  let flat_decls =
    match !input_file with
      | None -> (Printf.eprintf "%s\n" usage; exit 0)
      | Some f -> Parse_spec.parse_spec f in
  ignore flat_decls
