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

(* API for LSP *)
let json_out    = ref false

type common_opts =
  {co_debug:   bool;
   co_verbose: bool}

type check_opts =
  {co_show_raw_ast:      bool;
   co_show_parsed_ast:   bool;
   co_show_after_macros: bool;
   co_trace_solver:      bool;
   co_show_types:        bool;
   co_show_typed_ast:    bool;
   co_show_anf:          bool;
   co_trace_cfg_build:   bool;
   co_show_cfg:          bool;
   co_show_decorated:    string list;
   co_output_json:       bool}

let default_ckopts =
  {co_show_raw_ast      = false;
   co_show_parsed_ast   = false;
   co_show_after_macros = false;
   co_trace_solver      = false;
   co_show_types        = false;
   co_show_typed_ast    = false;
   co_show_anf          = false;
   co_trace_cfg_build   = false;
   co_show_cfg          = false;
   co_show_decorated    = [];
   co_output_json       = false}

type spec_opts =
  {so_import_dirs: string list}

let default_sopts =
  {so_import_dirs = []}

type exe_opts =
  {exe_show_data_as_ascii: bool;
   exe_trace_exec:         bool}

let process_copts copts =
  Printexc.record_backtrace copts.co_debug

module FD = Typing.Format_decorators
module StringSet = FD.StringSet

let process_ckopts ckopts =
  List.iter (fun s ->
      FD.display_decorated := StringSet.add s !FD.display_decorated
    ) ckopts.co_show_decorated;
  json_out := ckopts.co_output_json
