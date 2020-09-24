let handle_exception bt msg =
  Printf.fprintf stderr "%s\n" msg;
  Printf.printf "%s\n" bt

let check spec =
  let c = TypeInfer.generate_constraint spec in
  let env = ConstraintSolver.solve c in
  ConstraintSolver.print_env (TypeEnvPrinter.print_variable true) env

let type_check spec =
  try
    check spec
  with
    | TypingExceptions.Error e ->
        handle_exception
          (Printexc.get_backtrace ()) (TypingExceptions.error_msg e)
    | ConstraintSolver.Error e ->
        handle_exception
          (Printexc.get_backtrace ()) (ConstraintSolver.error_msg e)
