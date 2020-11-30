let handle_exception bt msg =
  Printf.fprintf stderr "%s\n" msg;
  Printf.printf "%s\n" bt

let trace_solver = false
let print_types  = false
let print_typed_ast = ref false

let get_tracer () =
  if trace_solver
  then Some (ConstraintSolver.tracer ())
  else None

let check spec =
  let c, spec' = TypeInfer.generate_constraint spec in
  let env = ConstraintSolver.solve ?tracer:(get_tracer ()) c in
  if print_types then
    ConstraintSolver.print_env
      (TypeEnvPrinter.print_variable true)
      env
  else
    ();
  if !print_typed_ast then
    AstPrinter.print_typed_spec spec'

let type_check spec_file spec =
  try
    check spec;
    Printf.printf "%s: parsed and typed.\n" spec_file
  with
    | TypingExceptions.Error e ->
        handle_exception
          (Printexc.get_backtrace ()) (TypingExceptions.error_msg e)
    | ConstraintSolver.Error e ->
        handle_exception
          (Printexc.get_backtrace ()) (ConstraintSolver.error_msg e)
    | Unifier.Error e ->
        handle_exception
          (Printexc.get_backtrace ()) (Unifier.error_msg e)
