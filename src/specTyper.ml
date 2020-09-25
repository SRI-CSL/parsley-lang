let handle_exception bt msg =
  Printf.fprintf stderr "%s\n" msg;
  Printf.printf "%s\n" bt

let trace_solver = true
let get_tracer () =
  if trace_solver
  then Some (ConstraintSolver.tracer ())
  else None

let check spec =
  let c = TypeInfer.generate_constraint spec in
  let env = ConstraintSolver.solve ?tracer:(get_tracer ()) c in
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
