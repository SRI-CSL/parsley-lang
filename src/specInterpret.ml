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
        Interpret.execute spec nt f
