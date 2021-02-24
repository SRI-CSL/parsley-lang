(**************************************************************************)
(*  This program is free software; you can redistribute it and/or modify  *)
(*  it under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation; version 2 of the License.               *)
(*                                                                        *)
(*  This program is distributed in the hope that it will be useful, but   *)
(*  WITHOUT ANY WARRANTY; without even the implied warranty of            *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU     *)
(*  General Public License for more details.                              *)
(*                                                                        *)
(*  You should have received a copy of the GNU General Public License     *)
(*  along with this program; if not, write to the Free Software           *)
(*  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA         *)
(*  02110-1301 USA                                                        *)
(*                                                                        *)
(**************************************************************************)

open Parsing
open Typing

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
  let tenv, venv, c = TypeInfer.init_env () in
  let c, tenv, spec' =
    TypeInfer.generate_constraint (tenv, venv, c) spec in
  let env = ConstraintSolver.solve ?tracer:(get_tracer ()) c in
  if print_types then
    ConstraintSolver.print_env
      (TypeEnvPrinter.print_variable true)
      env
  else
    ();
  if !print_typed_ast then
    AstPrinter.print_typed_spec TypeConstraintPrinter.print_crterm spec';
  tenv, spec'

let type_check spec_file spec =
  try
    let tenv, spec' = check spec in
    Pattern_match.check_patterns tenv spec';
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
