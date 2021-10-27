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

let print_ir = ref false

let handle_exception bt msg =
  Printf.fprintf stderr "%s\n" msg;
  Printf.printf "%s\n" bt;
  exit 1

let to_ir init_envs tenv (spec: Cfg.program) : Cfg.spec_ir =
  try
    let spec = Cfg_spec.lower_spec init_envs tenv spec in
    if !print_ir
    then Ir_printer.print_spec spec;
    spec
  with
    | Cfg_regexp.Error e ->
        handle_exception (Printexc.get_backtrace ()) (Cfg_regexp.error_msg e)
    | Anf.Error e ->
        handle_exception (Printexc.get_backtrace ()) (Anf.error_msg e)
