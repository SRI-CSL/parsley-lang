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

let generate_rust_parser_function_code ast = "Parsing gets done here...\n"

let parse_ast ast = rust_includes ^ rust_parser_function_start ^ (generate_rust_parser_function_code ast) ^ rust_parser_function_end
