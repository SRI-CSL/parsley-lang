let print_exception msg =
  Printf.fprintf stderr "%s\n" msg

let check spec =
  let c = TypeInfer.generate_constraint spec in
  let env = ConstraintSolver.solve c in
  ConstraintSolver.print_env (TypeEnvPrinter.print_variable true) env

let type_check spec =
  try
    check spec
  with TypingExceptions.Error e ->
    print_exception (TypingExceptions.error_msg e)
