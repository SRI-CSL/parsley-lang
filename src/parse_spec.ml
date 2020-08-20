open Ast
open Lexing
open Location

let print_exception f loc msg =
  Printf.fprintf f "%s: %s\n" (Location.str_of_loc loc) msg

let parse_file fname =
  let lexbuf = from_channel (open_in fname) in
  let lexbuf = { lexbuf with
                 lex_curr_p = { pos_fname = fname;
                                pos_lnum  = 1;
                                pos_bol   = 0;
                                pos_cnum  = 0 } } in
  try
    Parser.toplevel Lexer.token lexbuf
  with
    | Parser.Error ->
          (Printf.fprintf stderr "%s: parser error at or just before this location\n"
                          (Location.str_of_curr_pos lexbuf);
           exit 1)
    | Failure f ->
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
           | Decl_types l ->
               flatten (Flat_decl_types l :: accum) includes rest
           | Decl_fun f ->
               flatten (Flat_decl_fun f :: accum) includes rest
           | Decl_nterm n ->
               flatten (Flat_decl_nterm n :: accum) includes rest
           | Decl_format f ->
               flatten (Flat_decl_format f :: accum) includes rest
           | Decl_use u ->
               (match u.use_modules with
                  | [] -> flatten accum includes rest
                  | h :: t ->
                      (* pick the first, the others go back to pending *)
                      let pending_use = { u with use_modules = t } in
                      let pending = Decl_use pending_use :: rest in
                      let fname = Printf.sprintf "%s.ply" (Location.value h) in
                      if StringSet.mem fname includes then
                        (* we've already included this, skip *)
                        flatten accum includes pending
                      else
                        (*let _ = Printf.fprintf stdout " including %s ...\n" fname in*)
                        let ast = parse_file fname in
                        (* push its decls on top of the pending list *)
                        flatten accum (StringSet.add fname includes) (ast.decls @ pending)
               )
        )

let parse_spec f =
  (*Printf.fprintf stdout " parsing %s ...\n" f;*)
  let ast = parse_file f in
  flatten [] (StringSet.add f StringSet.empty) ast.decls
