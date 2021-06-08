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

let opt_print_ast = ref false
let input_file = ref []

let usage = Printf.sprintf
              "Usage: %s <options> <file.ply> " (Sys.argv.(0))
let options =
  Arg.align ([
        ( "-p",
          Arg.Set opt_print_ast,
          " print the parsed AST" )
      ])

let () =
  Printexc.record_backtrace false;
  Arg.parse options (fun s -> input_file := s :: !input_file) usage;
  if List.length !input_file > 1 || List.length !input_file = 0
  then (Printf.eprintf "Please specify a single input file.\n";
        exit 1);
  let spec_file = List.hd !input_file in
  let spec = SpecParser.parse_spec spec_file in
  if !opt_print_ast then
    Parsing.AstPrinter.print_parsed_spec spec;
  let init_envs, tenv, tspec = SpecTyper.type_check spec in
  SpecTyper.assignment_check init_envs tenv tspec;
  Printf.printf "%s: parsed and typed.\n" spec_file
