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

(* Parsing test driver. *)

open Parsing
open Ast
open Lexing
module I = Parser.MenhirInterpreter
open Interpreter

let handle_exception msg bt =
  Printf.fprintf stderr "%s\n%!" msg;
  Printf.printf "%s\n%!" bt;
  None

let parse_spec test s cont =
  let lexbuf = from_string s in
  let lexbuf = {lexbuf with
                 lex_curr_p = {pos_fname = test;
                               pos_lnum  = 1;
                               pos_bol   = 0;
                               pos_cnum  = 0}} in
  let start = Parser.Incremental.toplevel lexbuf.lex_curr_p in
  let supplier = I.lexer_lexbuf_to_supplier Lexer.token lexbuf in
  let fail chkpt =
    (* current current parser state *)
    let st =
      match chkpt with
        | I.HandlingError env ->
            I.current_state_number env
        | _ ->
            (* supposedly cannot happen *)
            assert false in
    let msg =
      try
        ParseErrorMessages.message st
      with Not_found ->
        Printf.sprintf "Unknown syntax error (in state %d)" st in
    Printf.fprintf stderr
      "%s: parser error at or just before this location:\n %s"
      (Location.str_of_curr_pos lexbuf) msg;
    None in
  try I.loop_handle cont fail supplier start
  with
    | Failure _f ->
        handle_exception
          (Printexc.get_backtrace ())
          (Printf.sprintf "%s: invalid token at or just before this location"
             (Location.str_of_curr_pos lexbuf))
    | Parseerror.Error (e, l) ->
        handle_exception
          (Printexc.get_backtrace ()) (Parseerror.error_msg l e)

let gen_ir (test_name: string) (spec: string) =
  let includes = SpecParser.StringSet.empty in
  let spec =
    parse_spec test_name spec (fun ast ->
        let ast = SpecParser.flatten false [] includes ast.pre_decls in
        Some {decls = List.rev ast}
      ) in
  match spec with
    | None   -> None
    | Some s -> let ies, te, ts = SpecTyper.type_check s in
                SpecTyper.assignment_check ies te ts;
                Some (SpecIR.to_ir ies te ts)

let exe_ir (test: string) (ir: Ir.Cfg.spec_ir) (entry: string) (data: string) =
  try  Interpret.execute_on_test_string test ir entry data
  with
    | Runtime_exceptions.Runtime_exception e ->
        (* Catch the backtrace before error_msg has an exception
           trying to open the fake input-file for the spec. *)
        handle_exception
          (Printf.sprintf "%s\n" (Runtime_exceptions.error_msg e))
          (Printexc.get_backtrace ())

let do_tests () =
  Tests.do_tests gen_ir exe_ir
