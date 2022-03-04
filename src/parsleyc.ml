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

let debug_build = false

let () =
  Printexc.record_backtrace debug_build;
  Options.process_options ();
  if   !Options.do_tests
  then (SpecTests.do_tests ();
        exit 0);
  if   List.length !Options.input_file > 1 || List.length !Options.input_file = 0
  then (Printf.eprintf "Please specify a single input file.\n";
        exit 1);
  let spec_file = List.hd !Options.input_file in
  let spec = SpecParser.parse_spec spec_file in
  if   !Options.print_ast
  then Parsing.AstPrinter.print_parsed_spec spec;
  let init_envs, tenv, tspec = SpecTyper.type_check spec in
  SpecTyper.assignment_check init_envs tenv tspec;
  let spec = SpecIR.to_ir init_envs tenv tspec in
  Printf.printf "%s: parsed, typed, generated IR.\n" spec_file;
  SpecInterpret.interpret spec !Options.ent_nonterm !Options.data_file
