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
open Flow
open Analysis

let handle_exception bt msg =
  Printf.fprintf stderr "%s\n" msg;
  Printf.printf "%s\n" bt;
  exit 1

let trace_solver = false
let print_types  = false
let print_typed_ast = ref false

let get_tracer () =
  if trace_solver
  then Some (ConstraintSolver.tracer ())
  else None

let check spec =
  let init_tenv, init_venv, c = TypeInfer.init_env () in
  let c, wc, tenv, spec' =
    TypeInfer.generate_constraint (init_tenv, init_venv, c) spec in
  let env = ConstraintSolver.solve ?tracer:(get_tracer ()) c in
  ConstraintSolver.check_width_constraints wc;
  if print_types then begin
      ConstraintSolver.print_env
        (TypeEnvPrinter.print_variable true)
        env;
      TypeConstraintPrinter.print_width_constraint wc
    end
  else
    ();
  if !print_typed_ast then
    AstPrinter.print_typed_spec TypeConstraintPrinter.print_crterm spec';
  (init_tenv, init_venv), tenv, spec'

let type_check spec =
  try
    let init_envs, tenv, spec' = check spec in
    Pattern_match.check_patterns tenv spec';
    init_envs, tenv, spec'
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

let assignment_check init_envs tenv tspec =
  try
    Analysis.Rulecfg.check_spec init_envs tenv tspec
  with
    | Graph.GraphError e ->
        handle_exception
          (Printexc.get_backtrace ()) (Graph.error_msg e)
    | Rulecfg.Error e ->
        handle_exception
          (Printexc.get_backtrace ()) (Rulecfg.error_msg e)
