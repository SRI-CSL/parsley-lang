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

let to_ir init_envs tenv (spec: Cfg.program) : Cfg.spec_ir =
  try
    let spec = Cfg_spec.lower_spec init_envs tenv spec in
    if   !Options.print_ir
    then Ir_printer.print_spec spec;
    spec
  with
    | Anf.Error (l, e) ->
        Errors.handle_exception (Printexc.get_backtrace ()) l (Anf.error_msg e)
    | Cfg_regexp.Error (l, e) ->
        Errors.handle_exception (Printexc.get_backtrace ()) l (Cfg_regexp.error_msg e)
    | Cfg.Error (l, e) ->
        Errors.handle_exception (Printexc.get_backtrace ()) l (Cfg.error_msg e)
