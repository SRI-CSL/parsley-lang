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
open Parsing.Ast
open Lexing
module I = Parser.MenhirInterpreter
open Typing

let parse_file fname cont =
  let lexbuf = from_channel (open_in fname) in
  let lexbuf = {lexbuf with
                 lex_curr_p = {pos_fname = fname;
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
    Errors.handle_exception "" (Location.loc_of_curr_lex lexbuf)
      (Printf.sprintf "parser error at or just before this location:\n %s"
         msg) in
  try
    I.loop_handle cont fail supplier start
  with
    | Failure _f ->
        Errors.handle_exception (Printexc.get_backtrace ()) (Location.loc_of_curr_lex lexbuf)
          "invalid token at or just before this location"
    | Parseerror.Error (e, l) ->
        Errors.handle_exception (Printexc.get_backtrace ()) l
          (Parseerror.error_msg e)

(* TODO: include directory management.
 * make this a list specifiable via cli -I options.
 * For now, just assume modules are in the same directory as the
 * top-level file. *)
let inc_dir = ref None
let update_inc_dir fname =
  match !inc_dir with
    | None ->
        let dirname = Filename.dirname fname in
        inc_dir := Some dirname
    | Some _ -> ()
let mk_filename modnm =
  let f = Printf.sprintf "%s.ply" modnm in
  match !inc_dir with
    | None   -> f
    | Some d -> Filename.concat d f

(* recursively include all the modules referenced by include
   declarations to generate a flattened declaration list *)
module StringSet = Set.Make(struct type t = string
                                   let compare = compare
                            end)
let rec flatten accum includes pending =
  match pending with
    | [] ->
        accum
    | d :: rest ->
        (match d with
           | PDecl_types (tl, l) ->
               flatten (PDecl_types (tl, l) :: accum) includes rest
           | PDecl_const c ->
               flatten (PDecl_const c :: accum) includes rest
           | PDecl_fun f ->
               flatten (PDecl_fun f :: accum) includes rest
           | PDecl_recfuns r ->
               flatten (PDecl_recfuns r :: accum) includes rest
           | PDecl_format f ->
               flatten (PDecl_format f :: accum) includes rest
           | PDecl_include i ->
               (match i with
                  | [] -> flatten accum includes rest
                  | h :: t ->
                      (* pick the first, the others go back to pending *)
                      let pending_incls = t in
                      let pending = PDecl_include pending_incls :: rest in
                      let fname = mk_filename (Location.value h) in
                      if StringSet.mem fname includes then
                        (* we've already included this, skip *)
                        flatten accum includes pending
                      else
                        (*let _ = Printf.fprintf stdout " including %s ...\n" fname in*)
                        parse_file fname (fun ast ->
                            (* push its decls on top of the pending list *)
                            flatten accum
                              (StringSet.add fname includes)
                              (ast.pre_decls @ pending)
                          )
               )
        )

let do_parse_spec f show_raw_ast : (unit, unit) spec_module =
  (*Printf.fprintf stdout " parsing %s ...\n" f;*)
  update_inc_dir f;

  (* set current module *)
  let m = AstUtils.modname_of_file f in
  (* check for conflict with stdlib *)
  if   TypeAlgebra.is_builtin_module m
  then (Printf.eprintf
          "Name error: Specification module `%s' conflicts with a standard library module.\n"
          m;
        Printf.eprintf "Consider renaming the specification file.\n";
        exit Cmdliner.Cmd.Exit.some_error);
  cur_module := Some m;

  let pre_ast: (unit, unit) pre_spec_module =
    parse_file f (fun ast ->
        let ast = flatten [] (StringSet.add f StringSet.empty) ast.pre_decls in
        {pre_decls = List.rev ast}
      ) in
  if   show_raw_ast
  then AstPrinter.print_raw_spec pre_ast;

  let bltins =
    Qualify_ast.({bltin_type    = TypeAlgebra.is_builtin_type;
                  bltin_field   = TypeAlgebra.is_builtin_field;
                  bltin_value   = TypeAlgebra.is_builtin_value;
                  bltin_nonterm = TypeAlgebra.is_builtin_nonterm}) in
  Qualify_ast.convert_spec bltins pre_ast

let parse_spec f show_raw_ast =
  try  do_parse_spec f show_raw_ast
  with
    | Sys_error s ->
        (Printf.eprintf "Error processing %s.\n" s;
         exit Cmdliner.Cmd.Exit.some_error)
    | Unix.Unix_error (e, op, _) ->
        (Printf.eprintf "Error processing %s: %s: %s.\n"
           f op (Unix.error_message e);
         exit Cmdliner.Cmd.Exit.some_error)
