open Fmt;;
open Location
open Ast
open Stdlib

let rust_includes = "\n use std::error::Error;
                    \n use std::fs::File;
                    \n use std::io::prelude::*;
                    \n use std::env;
                    \n use std::convert::TryInto;
                    \n use parsley_rust::pcore::parsebuffer::{ParseBuffer, ParsleyParser, Location};
                    \n use parsley_rust::pdf_lib::pdf_file::{HeaderP, StartXrefP, XrefSectP, XrefEntT};
                    \n use parsley_rust::pdf_lib::pdf_obj::{PDFObjContext, PDFObjT, PDFObjP};"

(* TODO: write a monad which handles the wrapping of brakcets *)
let rust_parser_function_start = "fn parse_file(test_file: &str) {\n"
let rust_parser_function_end = "\n}\n"

let comment_format_name ast =
  Printf.sprintf "// generating rust parser for %s format \n" ast.format_name.pelem;;


let generate_rust_parser_function_code ast = (comment_format_name ast) 


(*let parse_ast ast = rust_includes ^ rust_parser_function_start ^ (generate_rust_parser_function_code ast) ^ rust_parser_function_end *)

(* let parse_ast ast = pr "@[%s@]@." "hey";; ();;(\* (Stdlib.List.hd (ast.format_decls)).decl;; *\) *)

(*Pprint.print_ast Fmt.stdout ast;*)
let parse_ast ast = pr "%s" "hey ";; (* (Stdlib.List.hd (ast.format_decls)).decl;; *)
