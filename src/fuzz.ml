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
open Anfcfg
open Anfcfg_interpreter
open Fuzzer
(* open Fuzzer_interpreter *)

let interpret load_externals spec nt loop data_as_ascii =
  let _fmt_pos (o, e) =
    Printf.sprintf "offset %d (%d bytes remaining)" o (e - o) in
  let _fmt_stk nts =
    String.concat " <- " (List.map Location.value nts) in
  let do_once () =
    let (r, _e) = Fuzzer_interpreter.once_on_file load_externals spec nt in
    match r with
    | Cfg_ok v -> ( Printf.printf "fuzzer interpreter terminated successfully\n";
                    Printf.printf "%s\n%!" (Values.string_of_value data_as_ascii v);
                    exit Cmdliner.Cmd.Exit.ok;)
    | _ -> Printf.printf "fuzzer interpreter terminated successfully\n";
           exit Cmdliner.Cmd.Exit.some_error;
      (* | None -> (Printf.printf *)
      (*                         "Parse terminated in failure\n"; *)
      (*            exit Cmdliner.Cmd.Exit.some_error) *)
  in
  try
    if   loop
    then do_once ()
    else do_once ()
  with
    | Runtime_exceptions.Runtime_exception (l, e) ->
        Errors.handle_exception
          (Printexc.get_backtrace ()) l
          (Printf.sprintf "%s\n" (Runtime_exceptions.error_msg e))
    | Unix.Unix_error (_e, _op, _) ->
        Errors.handle_exception
          (Printexc.get_backtrace ())
          Parsing.Location.ghost_loc
          (Printf.sprintf "Error processing \n")

let fuzz _verbose (data_as_ascii: bool) (load_externals: bool)
      (loop: bool) (m: string) (start: string) (spec: Cfg.spec_cfg)
      (_data: string option) (_stdin: int option) =
  (* let inp_name, inp = *)
  (*   (\* match data, stdin with *\) *)
  (*   (\*   | None, None -> *\) *)
  (*   (\*       Errors.handle_exception "" Parsing.Location.ghost_loc *\) *)
  (*   (\*         (Printf.sprintf "No input specified.\n") *\) *)
  (*   (\*   | Some _, Some _ -> *\) *)
  (*   (\*       Errors.handle_exception "" Parsing.Location.ghost_loc *\) *)
  (*   (\*         (Printf.sprintf "Please specify only one input source.\n") *\) *)
  (*     | Some data_file, None -> *)
  (*         data_file, Fuzzer_interpreter.Inp_file data_file *)
  (*     | None, Some i -> *)
  (*         "stdin", Fuzzer_interpreter.Inp_stdin i in *)
  let m = Anf.M_name m in
  interpret load_externals spec (m, start) loop data_as_ascii
