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

open Ir
open Interpreter

let interpret spec nt f loop =
  let do_loop () =
    let vs = Interpret.loop_on_file spec nt f in
    let n  = List.length vs in
    Printf.printf "%d values extracted%s\n\n"
      n (if n = 0 then "." else ":");
    List.iter (fun v ->
        Printf.printf "%s\n\n%!" (Values.string_of_value v)
      ) vs in
  let do_once () =
    match Interpret.once_on_file spec nt f with
      | Some v -> (Printf.printf "Parse terminated successfully with:\n";
                   Printf.printf "%s\n%!" (Values.string_of_value v);
                   exit 0)
      | None   -> (Printf.printf "Parse terminated in failure.\n";
                   exit 1) in
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
             f op (Unix.error_message e))

let interpret (spec: Cfg.spec_ir) (ent_nonterm: string option)
      (data_file: string option) =
  match ent_nonterm, data_file with
    | None, None ->
        ()
    | Some nt, None ->
        Printf.eprintf "No data file specified to parse for `%s'.\n" nt
    | None, Some f ->
        Printf.eprintf "No entry non-terminal specified for `%s'.\n" f
    | Some nt, Some f ->
        interpret spec nt f !Options.loop
