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

(* command line and other tunable options *)

module FD = Typing.Format_decorators
module StringSet = FD.StringSet

let do_tests    = ref false
let print_ast   = ref false
let input_file  = ref []
let ent_nonterm = ref None
let data_file   = ref None
let json_out    = ref false

(* internal to specTyper *)
let print_post_macro = false
let trace_solver     = false
let print_types      = false
let print_typed_ast  = false

(* internal to specIR *)
let print_anf = ref false
let print_ir  = ref false

let options =
  Arg.align ([
        ( "-pa",
          Arg.Set print_ast,
          " print the parsed AST" );
        ( "-dd",
          Arg.String (fun s ->
              FD.display_decorated := StringSet.add s !FD.display_decorated
            ),
          " display the decorated non-terminal" );
        ( "-ir",
          Arg.Set print_ir,
          " print the IR" );
        ( "-ex",
          Arg.String (fun s -> ent_nonterm := Some s),
          " entry non-terminal to initiate parse" );
        ( "-df",
          Arg.String (fun s -> data_file := Some s),
          " data file to parse" );
        ( "-test",
          Arg.Set do_tests,
          " run internal tests");
        ( "-json",
          Arg.Set json_out,
          " output to stderr a json formatted string");
    ])

let usage = Printf.sprintf
              "Usage: %s <options> <file.ply> " (Sys.argv.(0))

let process_options () =
  Arg.parse options (fun s -> input_file := s :: !input_file) usage;
