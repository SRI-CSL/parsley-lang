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
module TypeAlgebra = Typing.TypeAlgebra

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

(* Source file naming. *)

let mk_src_filename f =
  Printf.sprintf "%s.ply" f

(* Include files are resolved in the same directory as the top-level
   source file. *)
let inc_dir = ref None

let set_inc_dir d =
  inc_dir := Some d

let mk_inc_filename f =
  let f = mk_src_filename f in
  match !inc_dir with
    | None   -> f
    | Some d -> Filename.concat d f

(* Recursively include all the modules referenced by include
   declarations to generate a flattened declaration list. *)

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)
type imports = ident StringMap.t

let rec flatten ((decls, imps) as accum) includes pending =
  match pending with
    | [] ->
        accum
    | d :: rest ->
        (match d with
           | PDecl_types (tl, l) ->
               flatten (PDecl_types (tl, l) :: decls, imps) includes rest
           | PDecl_const c ->
               flatten (PDecl_const c :: decls, imps) includes rest
           | PDecl_fun f ->
               flatten (PDecl_fun f :: decls, imps) includes rest
           | PDecl_recfuns r ->
               flatten (PDecl_recfuns r :: decls, imps) includes rest
           | PDecl_foreign fs ->
               flatten (PDecl_foreign fs :: decls, imps) includes rest
           | PDecl_format f ->
               flatten (PDecl_format f :: decls, imps) includes rest
           | PDecl_include i ->
               (match i with
                  | [] -> flatten accum includes rest
                  | h :: t ->
                      (* Pick the first, the others go back to pending. *)
                      let pending_incls = t in
                      let pending = PDecl_include pending_incls :: rest in
                      let fname = mk_inc_filename (Location.value h) in
                      if StringSet.mem fname includes then
                        (* We've already included this, skip. *)
                        flatten accum includes pending
                      else
                        (*let _ = Printf.fprintf stdout " including %s ...\n" fname in*)
                        parse_file fname (fun ast ->
                            (* Push its decls on top of the pending list. *)
                            flatten accum
                              (StringSet.add fname includes)
                              (ast.pre_decls @ pending)
                          )
               )
           | PDecl_import i ->
               let imps = List.fold_left (fun imps i ->
                              let m = Location.value i in
                              StringMap.add m i imps
                            ) imps i in
               flatten (decls, imps) includes rest
        )

let do_parse_spec f show_raw_ast : (unit, unit) pre_spec_module * imports =
  (*Printf.fprintf stdout " parsing %s ...\n" f;*)

  (* Set current module. *)
  let m = AstUtils.modname_of_file f in
  (* Check for conflict with stdlib. *)
  if   TypeAlgebra.is_builtin_module m
  then (Printf.eprintf
          "Name error: Specification module `%s' conflicts with a standard library module.\n"
          m;
        Printf.eprintf "Consider renaming the specification file.\n";
        exit Cmdliner.Cmd.Exit.some_error);
  set_cur_module m;

  let (pre_ast, imports): (unit, unit) pre_spec_module * ident StringMap.t =
    parse_file f (fun ast ->
        let ast, imps =
          flatten ([], StringMap.empty) (StringSet.add f StringSet.empty) ast.pre_decls in
        {pre_decls = List.rev ast}, imps
      ) in
  if   show_raw_ast
  then AstPrinter.print_raw_spec pre_ast;

  pre_ast, imports

let qualify_spec pre_ast imports : (unit, unit) spec_module =
  let bltins =
    Qualify_ast.({bltin_type    = TypeAlgebra.is_builtin_type;
                  bltin_field   = TypeAlgebra.is_builtin_field;
                  bltin_value   = TypeAlgebra.is_builtin_value;
                  bltin_nonterm = TypeAlgebra.is_builtin_nonterm}) in
  Qualify_ast.convert_spec bltins imports pre_ast

let parse_single_spec f show_raw_ast =
  try  let pre_ast, imports = do_parse_spec f show_raw_ast in
       imports, qualify_spec pre_ast imports
  with
    | Sys_error s ->
        (Printf.eprintf "Error processing %s.\n" s;
         exit Cmdliner.Cmd.Exit.some_error)
    | Unix.Unix_error (e, op, _) ->
        (Printf.eprintf "Error processing %s: %s: %s.\n"
           f op (Unix.error_message e);
         exit Cmdliner.Cmd.Exit.some_error)
    | Qualify_ast.Error (l, e) ->
        Errors.handle_exception (Printexc.get_backtrace ()) l (Qualify_ast.error_msg e)

(* The dependency graph is built from the modules specified in the
   import declarations. *)
module DG = Depgraph.Make(struct type t = ident
                                 let compare m1 m2 =
                                   let n1 = Location.value m1 in
                                   let n2 = Location.value m2 in
                                   compare n1 n2
                          end)

(* Intermediate output of spec builder. *)
type build =
  (unit, unit) spec_module StringMap.t (* qualified specs *)
  * DG.t                               (* import dependency graph *)

(* Builder state. *)
type state =
  ident StringMap.t (* pending imports to process *)
  * build           (* current build *)

type error =
  | Import_cycle of ident list
  | Cap_conflict of ident * string * string
  | Source_file_not_found of ident

exception Build_error of Location.t * error

(* Import directories. *)
let import_dirs : string list ref = ref []
let add_import_dir d =
  import_dirs := d :: !import_dirs

(* This maps a import module name to a top-level spec-file. *)
let resolve_module_file (mod_name: ident) : string =
  (* Module names are capitalized, but their origin source-files may
     or may not have capitalization.  To avoid confusion, we should
     raise an error if both versions are present.

     However, filesystems like MacOSX are case insensitive, so disable
     this check.  Leave the code in place in case we can incorporate a
     clean way of detecting case-insensitive file systems. *)
  let cap_name = String.capitalize_ascii (Location.value mod_name) in
  let low_name = String.uncapitalize_ascii cap_name in
  let in_dir d name =
    let fname  = mk_src_filename name in
    let path   = Filename.concat d fname in
    let exists = Sys.file_exists path in
    let is_dir = if   exists
                 then Sys.is_directory path
                 else false in
    exists && (not is_dir), path in
  let choose_cap d =
    let have_cap, cap_path = in_dir d cap_name in
    let have_low, low_path = in_dir d low_name in
    if      have_cap && have_low && false
    then    let err = Cap_conflict (mod_name, cap_path, low_path) in
            raise (Build_error (Location.loc mod_name, err))
    else if have_cap
    then    Some cap_path
    else if have_low
    then    Some low_path
    else    None in
  let rec try_dirs dirs =
    match dirs with
      | d :: rest -> (match choose_cap d with
                        | None   -> try_dirs rest
                        | Some p -> d, p)
      | []        -> let err = Source_file_not_found mod_name in
                     let loc = Location.loc mod_name in
                     raise (Build_error (loc, err)) in
  let d, p = try_dirs !import_dirs in
  (* Set the include directory for files included by this module. *)
  set_inc_dir d;
  p

(* Given a name for a top-level spec module and its source file, and
   the current building state: parse that spec, collect its imports,
   qualify the spec, and update the state with the imports and
   qualified spec. *)
let builder_step (st: state) (mod_name: modident) (file: string)
      (show_raw_ast: bool)
    : state =
  let pending, (processed, depgraph) = st in
  let imports, spec = parse_single_spec file show_raw_ast in
  let processed =
    StringMap.add (Location.value mod_name) spec processed in
  let pending = StringMap.fold (fun m imp pending ->
                    if   StringMap.mem m processed
                    then pending
                    else StringMap.add m imp pending
                  ) imports pending in
  let deps = List.map snd (StringMap.bindings imports) in
  match DG.add_deps depgraph mod_name deps with
    | Error cycle -> let err = Import_cycle cycle in
                     let loc = Location.loc mod_name in
                     raise (Build_error (loc, err))
    | Ok depgraph -> pending, (processed, depgraph)

(* Given the name of the top-level spec file, parse it and all its
   transitive imports, to generate a collection of specifications
   indexed by their module names, and a import dependency graph. *)
let build_spec_info (top_spec_file: string) show_raw_ast : build =
  (* Loop to build all pending imports. *)
  let rec loop (pending, (processed, depgraph)) =
    match StringMap.choose_opt pending with
      | None   ->
          processed, depgraph
      | Some (mod_name, mod_import) ->
          let pending = StringMap.remove mod_name pending in
          let file = resolve_module_file mod_import in
          let st = pending, (processed, depgraph) in
          let st = builder_step st mod_import file show_raw_ast in
          loop st in
  (* The top-spec is given as a file-name; generate the corresponding
     module name. *)
  let mod_name  = AstUtils.modname_of_file top_spec_file in
  let top_mod   = Location.mk_ghost mod_name in
  (* Add the top-spec's directory to the include list. *)
  add_import_dir (Filename.dirname top_spec_file);
  (* Initialize the builder state. *)
  let pending   = StringMap.singleton mod_name top_mod in
  let processed = StringMap.empty in
  let depgraph  = DG.init in
  let init_st   = pending, (processed, depgraph) in
  (* Build. *)
  loop init_st

let mk_flat_spec ((specs, depgraph): build)
    : (unit, unit) spec_module =
  (* Order the specs in dependency order. *)
  let dep_order = match DG.topo_sort depgraph with
      | Error cycle -> let err = Import_cycle cycle in
                       let loc = Location.ghost_loc in
                       raise (Build_error (loc, err))
      | Ok deps     -> deps in
  let ordered_specs : (unit, unit) spec_module list =
    List.map (fun m ->
        let mod_name = Location.value m in
        match StringMap.find_opt mod_name specs with
          | Some s -> s
          | None   -> Printf.eprintf "Cannot find spec for `%s'.\n" mod_name;
                      assert false
      ) dep_order in
  (* Splice the specs into one. *)
  let decls =
    List.concat (List.map (fun s -> s.decls) ordered_specs) in
  {decls = decls}

let error_msg (e: error) : string =
  match e with
    | Import_cycle mods ->
        let cycle =
          String.concat " -> " (List.map Location.value mods) in
        Printf.sprintf "Import loop detected: %s." cycle
    | Cap_conflict (m, p1, p2) ->
        Printf.sprintf "File conflict for module `%s': `%s' conflicts with `%s'."
          (Location.value m) p1 p2
    | Source_file_not_found m ->
        Printf.sprintf "Source file for module `%s' not found."
          (Location.value m)

(* Entry point. *)
let build_spec (top_spec_file: string) (sopts: Options.spec_opts) show_raw_ast
    : (unit, unit) spec_module =
  import_dirs := sopts.so_import_dirs;
  try
    let info = build_spec_info top_spec_file show_raw_ast in
    mk_flat_spec info
  with
    | Build_error (l, e) ->
        Errors.handle_exception (Printexc.get_backtrace ()) l (error_msg e)
