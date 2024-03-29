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
open Cmdliner
open Options

(* TODO: needs to be auto-generated *)
let version = "0.2.0"

(* implementation of top-level commands *)

let test copts : unit =
  Options.process_copts copts;
  Test.run_tests copts.co_verbose Test.gen_cfg Test.exe_cfg

let test2 copts : unit =
  Options.process_copts copts;
  Test2.run_tests copts.co_verbose Test2.gen_scf Test2.exe_scf

let check copts ckopts sopts spec_file : unit =
  Options.process_copts copts;
  Options.process_ckopts ckopts;
  Check.check_spec copts.co_verbose ckopts sopts spec_file

let check2 copts ckopts sopts spec_file : unit =
  Options.process_copts copts;
  Options.process_ckopts ckopts;
  Check2.check_spec copts.co_verbose ckopts sopts spec_file

let execute copts sopts xopts load_externals loop start
      spec_file data_file stdin : unit =
  Options.process_copts copts;
  let verbose = copts.co_verbose in
  let ckopts = Options.default_ckopts in
  let spec = Check.cfg_of_spec verbose ckopts sopts spec_file in
  let m = Parsing.AstUtils.modname_of_file spec_file in
  Execute.execute verbose xopts.exe_show_data_as_ascii
    load_externals loop m start spec data_file stdin

let execute2 copts sopts xopts load_externals loop start
      spec_file data_file stdin : unit =
  Options.process_copts copts;
  let verbose = copts.co_verbose in
  let ckopts = Options.default_ckopts in
  let spec = Check2.scf_of_spec verbose ckopts sopts spec_file in
  let m = Parsing.AstUtils.modname_of_file spec_file in
  Execute2.execute verbose xopts.exe_show_data_as_ascii xopts.exe_trace_exec
    load_externals loop m start spec data_file stdin

(* TODO: help command *)

(* CLI arguments *)

let mk_copts co_debug co_verbose : common_opts = {co_debug; co_verbose}

let copts_t : common_opts Term.t =
  let docs = Manpage.s_common_options in
  let debug =
    let doc = "Enable debug mode to help diagnose internal errors." in
    Arg.(value & flag & info ["d"; "debug"] ~docs ~doc) in
  let verb =
    let doc = "Enable verbose mode." in
    Arg.(value & flag & info ["v"; "verbose"] ~docs ~doc) in
  Term.(const mk_copts $ debug $ verb)

let mk_ckopts co_trace_solver co_show_raw_ast co_show_parsed_ast
      co_show_after_macros co_show_types co_show_typed_ast co_show_anf
      co_trace_cfg_build co_show_cfg co_show_decorated
    : check_opts =
  {co_show_raw_ast;
   co_show_parsed_ast;
   co_show_after_macros;
   co_trace_solver;
   co_show_types;
   co_show_typed_ast;
   co_trace_cfg_build;
   co_show_anf;
   co_show_cfg;
   co_show_decorated}

let ckopts_t : check_opts Term.t =
  let trace_solver =
    let doc = "Trace the type constraint solver." in
    Arg.(value & flag & info ["trace-solver"] ~doc) in
  let show_raw_ast =
    let doc = "Show the raw AST of the specification." in
    Arg.(value & flag & info ["show-raw-ast"] ~doc) in
  let show_parsed_ast =
    let doc = "Show the parsed AST of the specification." in
    Arg.(value & flag & info ["show-parsed-ast"] ~doc) in
  let show_after_macros =
    let doc = "Show the parsed AST of the specification after macro expansion." in
    Arg.(value & flag & info ["show-after-macros"] ~doc) in
  let show_types =
    let doc = "Show the types of the top-level variables in the specification." in
    Arg.(value & flag & info ["show-types"] ~doc) in
  let show_typed_ast =
    let doc = "Show the AST annotated with the solved types." in
    Arg.(value & flag & info ["show-typed-ast"] ~doc) in
  let show_anf =
    let doc = "Show the generated A-Normal form for the expression sublanguage." in
    Arg.(value & flag & info ["show-anf"] ~doc) in
  let trace_cfg_build =
    let doc = "Trace the construction of the generated control flow graph for the grammar sublanguage." in
    Arg.(value & flag & info ["trace-cfg-build"] ~doc) in
  let show_cfg =
    let doc = "Show the generated control flow graph for the grammar sublanguage." in
    Arg.(value & flag & info ["show-cfg"] ~doc) in
  let show_decorated =
    let docv = "NonTerm" in
    let doc  = "Show the decorated version of the specified non-terminal." in
    Arg.(value & opt_all string [] & info ["show-decorated"] ~doc ~docv) in
  Term.(const mk_ckopts $ trace_solver $ show_raw_ast $ show_parsed_ast
        $ show_after_macros $ show_types $ show_typed_ast
        $ show_anf $ trace_cfg_build $ show_cfg $ show_decorated)

let mk_sopts so_import_dirs : spec_opts =
  {so_import_dirs}

let sopts_t : spec_opts Term.t =
  let import_dir =
    let docv = "dir" in
    let doc  = "Import directory." in
    Arg.(value & opt_all dir [] & info ["I"] ~doc ~docv) in
  Term.(const mk_sopts $ import_dir)

let spec : string Term.t =
  let docv = "spec_file" in
  let doc  = "The file containing the input Parsley specification." in
  Arg.(required & (pos 0 (some non_dir_file) None & info [] ~doc ~docv))

let mk_exopts exe_show_data_as_ascii exe_trace_exec: exe_opts =
  {exe_show_data_as_ascii;
   exe_trace_exec}

let exopts_t : exe_opts Term.t =
  let show_data_as_ascii =
    let doc = "Interpret byte data as (ascii) strings." in
    Arg.(value & flag & info ["show-data-as-ascii"] ~doc) in
  let trace_exec =
    let doc = "Trace execution." in
    Arg.(value & flag & info ["trace-exec"] ~doc) in
  Term.(const mk_exopts $ show_data_as_ascii $ trace_exec)

let data : string option Term.t =
  let docv = "data_file" in
  let doc  = "The file with input data in the specified format." in
  Arg.(value & (pos 1 (some non_dir_file) None & info [] ~doc ~docv))

let stdin : int option Term.t =
  let doc = "Use standard input as data file, starting with the specified minimum number of bytes." in
  Arg.(value & (opt (some int) None & info ["p"; "stdin"] ~doc))

let start : string Term.t =
  let docv = "Start" in
  let doc  = "The start (or entry) non-terminal for the parse." in
  Arg.(required & (opt (some string) None & info ["s"; "start"] ~doc ~docv))

let load_externals : bool Term.t =
  let doc = "Load foreign function implementations." in
  Arg.(value & flag & info ["f"; "with-foreign"] ~doc)

let loop : bool Term.t =
  let doc = "Parse the data as repeated instances of the given format." in
  Arg.(value & flag & info ["l"; "loop"] ~doc)

(* CLI commands *)

let test_cmd : unit Cmd.t =
  let doc  = "run internal tests" in
  let info = Cmd.info "test" ~doc in
  Cmd.v info Term.(const test $ copts_t)

let test2_cmd : unit Cmd.t =
  let doc  = "run internal tests" in
  let info = Cmd.info "test2" ~doc in
  Cmd.v info Term.(const test2 $ copts_t)

let check_cmd : unit Cmd.t =
  let doc  = "parse, type-check and generate IR for a specification" in
  let info = Cmd.info "check" ~doc in
  Cmd.v info Term.(const check $ copts_t $ ckopts_t $ sopts_t $ spec)

let check2_cmd : unit Cmd.t =
  let doc  = "parse, type-check and generate IR for a specification" in
  let info = Cmd.info "check2" ~doc in
  Cmd.v info Term.(const check2 $ copts_t $ ckopts_t $ sopts_t $ spec)

let execute_cmd : unit Cmd.t =
  let doc  = "parse the given data using the given specification" in
  let info = Cmd.info "execute" ~doc in
  Cmd.v info Term.(const execute $ copts_t $ sopts_t $ exopts_t
                   $ load_externals $ loop $ start $ spec $ data $ stdin)

let execute2_cmd : unit Cmd.t =
  let doc  = "parse the given data using the given specification" in
  let info = Cmd.info "execute2" ~doc in
  Cmd.v info Term.(const execute2 $ copts_t $ sopts_t $ exopts_t
                   $ load_externals $ loop $ start $ spec $ data $ stdin)

(* top-level command *)
let main_cmd : unit Cmd.t =
  let doc  = "the Parsley compiler" in
  let prog = Filename.basename Sys.argv.(0) in
  let info = Cmd.info prog ~version:version ~doc in
  Cmd.group info [check_cmd; execute_cmd; test_cmd;
                  check2_cmd; execute2_cmd; test2_cmd]

let run () =
  exit (Cmd.eval main_cmd)
