open Parsing
open Parsing.Ast
open Lexing
module I = Parser.MenhirInterpreter

let print_exception f loc msg =
  Printf.fprintf f "%s: %s\n" (Location.str_of_loc loc) msg

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
    Printf.fprintf stderr
      "%s: parser error at or just before this location:\n %s"
      (Location.str_of_curr_pos lexbuf) msg;
    exit 1 in
  try
    I.loop_handle cont fail supplier start
  with
    | Failure _f ->
          (let _bt = Printexc.get_backtrace () in
           Printf.fprintf stderr "%s: invalid token at or just before this location\n"
                          (Location.str_of_curr_pos lexbuf);
           (* Printf.fprintf stderr " %s\n" _bt; *)
           exit 1)
    | Lexer.Error (e, l) ->
          (print_exception stderr l (Lexer.error_string e);
           exit 1)
    | Parseerror.Error (e, l) ->
          (print_exception stderr l (Parseerror.error_string e);
           exit 1)


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
    | None -> f
    | Some d -> Filename.concat d f

(* recursively include all the modules referenced by use declarations
 * to generate a flattened declaration list *)
module StringSet = Set.Make(struct type t = string
                                   let compare = compare
                            end)
let rec flatten accum includes pending =
  match pending with
    | [] -> accum
    | d :: rest ->
        (match d with
           | PDecl_types (tl, l) ->
               flatten (Decl_types (tl, l) :: accum) includes rest
           | PDecl_fun f ->
               flatten (Decl_fun f :: accum) includes rest
           | PDecl_format f ->
               flatten (Decl_format f :: accum) includes rest
           | PDecl_use u ->
               (match u.use_modules with
                  | [] -> flatten accum includes rest
                  | h :: t ->
                      (* pick the first, the others go back to pending *)
                      let pending_use = {u with use_modules = t} in
                      let pending = PDecl_use pending_use :: rest in
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

let parse_spec f =
  (*Printf.fprintf stdout " parsing %s ...\n" f;*)
  update_inc_dir f;
  parse_file f (fun ast ->
      let ast = flatten [] (StringSet.add f StringSet.empty) ast.pre_decls in
      {decls = List.rev ast}
    )
