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
  let fmt_pos (o, e) =
    Printf.sprintf "offset %d (%d bytes remaining)" o (e - o) in
  let do_loop () =
    let vs, lp = Interpret.loop_on_file spec nt f in
    let n = List.length vs in
    Printf.printf "%d values extracted with parse terminating at %s%s\n\n"
      n (fmt_pos lp) (if n = 0 then "." else ":");
    List.iter (fun v ->
        Printf.printf "%s\n\n%!" (Values.string_of_value v)
      ) vs in
  let do_once () =
    match Interpret.once_on_file spec nt f with
      | Some v, lp -> (Printf.printf
                         "Parse terminated successfully at %s with:\n"
                         (fmt_pos lp);
                       Printf.printf "%s\n%!" (Values.string_of_value v);
                       exit Cmdliner.Cmd.Exit.ok)
      | None, lp   -> (Printf.printf
                         "Parse terminated in failure at %s.\n"
                         (fmt_pos lp);
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
             f op (Unix.error_message e))

let execute _verbose (loop: bool) (m: string) (start: string)
      (spec: Cfg.spec_ir) (data: string) =
  let m = Anf.M_name m in
  interpret spec (m, start) data loop
