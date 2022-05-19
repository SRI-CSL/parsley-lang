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
open Ir
open Options

let parse_spec ckopts spec_file =
  let spec = SpecParser.parse_spec spec_file ckopts.co_show_raw_ast in
  if   ckopts.co_show_parsed_ast
  then AstPrinter.print_parsed_spec spec;
  spec

let checker ckopts spec =
  let tracer = if   ckopts.co_trace_solver
               then Some (ConstraintSolver.tracer ())
               else None in
  let spec = Macros.expand_spec spec in
  if   ckopts.co_show_after_macros
  then AstPrinter.print_parsed_spec spec;
  let init_tenv, init_venv, c = TypeInfer.init_env () in
  let c, wc, tenv, spec' =
    TypeInfer.generate_constraint (init_tenv, init_venv, c) spec in
  let env = ConstraintSolver.solve ?tracer c in
  ConstraintSolver.check_width_constraints wc;
  if   ckopts.co_show_types
  then (ConstraintSolver.print_env
          (TypeEnvPrinter.print_variable true)
          env;
        TypeConstraintPrinter.print_width_constraint wc)
  else ();
  if   ckopts.co_show_typed_ast
  then AstPrinter.print_typed_spec TypeConstraintPrinter.print_crterm spec';
  let init_envs = init_tenv, init_venv in
  Pattern_match.check_patterns tenv spec';
  Analysis.Rulecfg.check_spec init_envs tenv spec';
  init_envs, tenv, spec'

let type_check ckopts spec =
  try  checker ckopts spec
  with
    (* error messages from conversion of regexp literals *)
    | Literal_lexer.Error (l, e) ->
        Errors.handle_exception (Printexc.get_backtrace ()) l (Literal_lexer.error_msg e)
    | TypingExceptions.Error (l, e) ->
        Errors.handle_exception
          (Printexc.get_backtrace ()) l (TypingExceptions.error_msg e)
    | ConstraintSolver.Error (l, e) ->
        Errors.handle_exception
          (Printexc.get_backtrace ()) l (ConstraintSolver.error_msg e)
    | Unifier.Error (l, e) ->
        Errors.handle_exception
          (Printexc.get_backtrace ()) l (Unifier.error_msg e)
    | Graph.GraphError e ->
        Errors.handle_exception
          (Printexc.get_backtrace ()) Location.ghost_loc (Graph.error_msg e)
    | Rulecfg.Error (l, e) ->
        Errors.handle_exception
          (Printexc.get_backtrace ()) l (Rulecfg.error_msg e)

let mk_ir ckopts init_envs tenv (spec: Cfg.spec_module) : Cfg.spec_ir =
  try  Cfg_spec.lower_spec init_envs tenv spec ckopts.co_show_anf
  with
    | Anf.Error (l, e) ->
        Errors.handle_exception (Printexc.get_backtrace ()) l (Anf.error_msg e)
    | Cfg_regexp.Error (l, e) ->
        Errors.handle_exception (Printexc.get_backtrace ()) l (Cfg_regexp.error_msg e)
    | Cfg.Error (l, e) ->
        Errors.handle_exception (Printexc.get_backtrace ()) l (Cfg.error_msg e)

let ir_of_ast _verbose ckopts ast : Cfg.spec_ir =
  let init_envs, tenv, tspec = type_check ckopts ast in
  let ir = mk_ir ckopts init_envs tenv tspec in
  if   ckopts.co_show_cfg
  then Ir_printer.print_spec ir;
  ir

let ir_of_spec verbose ckopts spec_file : Cfg.spec_ir =
  let ast = parse_spec ckopts spec_file in
  ir_of_ast verbose ckopts ast

let check_spec verbose ckopts spec_file : unit =
  ignore (ir_of_spec verbose ckopts spec_file)
