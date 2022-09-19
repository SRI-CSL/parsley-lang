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

let interpret load_externals spec nt inp_name inp loop data_as_ascii =
  let fmt_pos (o, e) =
    Printf.sprintf "offset %d (%d bytes remaining)" o (e - o) in
  let fmt_stk nts =
    String.concat " <- " (List.map Location.value nts) in
  let do_loop () =
    let vs, (lp, _) = Interpret.loop_on_file load_externals spec nt inp in
    let n = List.length vs in
    Printf.printf "%d values extracted with parse terminating at %s%s\n\n"
      n (fmt_pos lp) (if n = 0 then "." else ":");
    List.iter (fun v ->
        Printf.printf "%s\n\n%!"
          (Values.string_of_value data_as_ascii v)
      ) vs in
  let do_once () =
    match Interpret.once_on_file load_externals spec nt inp with
      | Some v, (lp, _) -> (Printf.printf
                              "Parse terminated successfully at %s with:\n"
                              (fmt_pos lp);
                            Printf.printf "%s\n%!"
                              (Values.string_of_value data_as_ascii v);
                            exit Cmdliner.Cmd.Exit.ok)
      | None, (lp, stk) -> (Printf.printf
                              "Parse terminated in failure at %s\nwith parse stack: %s.\n"
                              (fmt_pos lp) (fmt_stk stk);
                            exit Cmdliner.Cmd.Exit.some_error) in
  try
    if   loop
    then do_loop ()
    else do_once ()
  with
    | Runtime_exceptions.Runtime_exception (l, e) ->
        Errors.handle_exception
          (Printexc.get_backtrace ()) l
          (Printf.sprintf "%s\n" (Runtime_exceptions.error_msg e))
    | Unix.Unix_error (e, op, _) ->
        Errors.handle_exception
          (Printexc.get_backtrace ())
          Parsing.Location.ghost_loc
          (Printf.sprintf "Error processing %s: %s: %s.\n"
             inp_name op (Unix.error_message e))

let execute _verbose (data_as_ascii: bool) (load_externals: bool)
      (loop: bool) (m: string) (start: string) (spec: Cfg.spec_cfg)
      (data: string option) (stdin: int option) =
  let inp_name, inp =
    match data, stdin with
      | None, None ->
          Errors.handle_exception "" Parsing.Location.ghost_loc
            (Printf.sprintf "No input specified.\n")
      | Some _, Some _ ->
          Errors.handle_exception "" Parsing.Location.ghost_loc
            (Printf.sprintf "Please specify only one input source.\n")
      | Some data_file, None ->
          data_file, Interpret.Inp_file data_file
      | None, Some i ->
          "stdin", Interpret.Inp_stdin i in
  let m = Anf.M_name m in
  interpret load_externals spec (m, start) inp_name inp loop data_as_ascii
