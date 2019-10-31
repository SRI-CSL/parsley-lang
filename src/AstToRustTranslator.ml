open Location
open Ast
    
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

let tmp_fun x =
  let a,b,c = get_pos_info x.ploc.loc_start in
  Printf.sprintf "%s %d %d" a b c;;

let comment_format_name ast =
  Printf.sprintf "// generating rust parser for %s format \n" ast.format_name.pelem;;

let print_decl_use decl_use =
  Printf.sprintf "decl_use: %s \n" decl_use.use_module.pelem

let print_non_term_varname = function
  | Some x -> Printf.sprintf "non-term-var-name %s\n" x.pelem
  | None -> "non-term-var-name: empty here"
    
let print_type_expr = function
  | TE_path p -> "TE apth\n"
  | _ -> "type expr otherwise\n"

let print_param_decl x = "skip-param decl"

  (* (? takes a function) x.pelem.type_expr *)

let rec print_non_term_inh_attrs = function 
  | [] -> "EOL/empty non term arrts\n"
  | hd :: tl -> (print_param_decl hd) ^ "-" ^ (print_non_term_inh_attrs tl)

let print_non_term_syn_attrs a = String.concat "+" (List.map print_param_decl a);;

let rec print_rule_elem r = print_rule_elem_desc r.rule_elem
and print_rule_elem_desc = function
  | RE_literal a -> Printf.sprintf "%s " a.pelem
  | RE_seq a -> String.concat "-seq-" (List.map print_rule_elem a)
  | RE_star  a -> print_rule_elem a
  | _ -> "etc rule elem";;

let rec print_rule r = "\nrule:"
                       ^ (String.concat "+" (List.map print_rule_elem r.rule_rhs))
                       ^ (String.concat "+" (List.map print_param_decl r.rule_temps))
                         ^ "EOR\n"

let print_non_term_rules a = String.concat "+" (List.map print_rule a);;

let print_decl_non_term a =
  Printf.sprintf "non-term-decl: %s\n" a.non_term_name.pelem
  ^ print_non_term_varname a.non_term_varname
  ^ print_non_term_inh_attrs a.non_term_inh_attrs
  ^ print_non_term_syn_attrs a.non_term_syn_attrs
  ^ print_non_term_rules a.non_term_rules

let print_decl = function
  | Decl_use x -> print_decl_use x
  | Decl_non_term y -> print_decl_non_term y
  | _ -> "other type"

let generate_rust_parser_function_code ast =
  (comment_format_name ast) ^ (String.concat "+" (List.map (fun x -> print_decl x.decl) ast.format_decls
))

let parse_ast ast = rust_includes ^ rust_parser_function_start ^ (generate_rust_parser_function_code ast) ^ rust_parser_function_end
