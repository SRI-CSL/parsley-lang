open Fmt
open Location
open Ast
open Stdlib

let pprint_ploc fmt l =
  let x, y, z = get_pos_info l.loc_start
  in pf fmt "Location: \n loc_start_pos: %s %d %d" x y z

(*_FIXME: how to rpint this?*)
let pprint_pelem fmt pelem = "";;

let pprint_location fmt loc = pprint_ploc fmt loc.ploc

(* START *)
let pprint_decl_use decl_use =
  str "decl_use: %s \n" decl_use.use_module.pelem

let pprint_non_term_varname = function
  | Some x -> Printf.sprintf "non-term-var-name %s\n" x.pelem
  | None -> "non-term-var-name: empty here"

let pprint_type_expr = function
  | TE_path p -> "TE apth\n"
  | _ -> "type expr otherwise\n"

let pprint_param_decl x = "skip-param decl"

  (* (? takes a function) x.pelem.type_expr *)

let rec pprint_non_term_inh_attrs = function
  | [] -> "EOL/empty non term arrts\n"
  | hd :: tl -> (pprint_param_decl hd) ^ "-" ^ (pprint_non_term_inh_attrs tl)

let pprint_non_term_syn_attrs a = String.concat "+" (List.map pprint_param_decl a);;

let rec pprint_rule_elem r = pprint_rule_elem_desc r.rule_elem
and pprint_rule_elem_desc = function
  | RE_literal a -> Printf.sprintf "%s " a.pelem
  | RE_seq a -> String.concat "-seq-" (List.map pprint_rule_elem a)
  | RE_star  a -> pprint_rule_elem a
  | _ -> "etc rule elem";;

let rec print_rule r = "\nrule:"
                       ^ (String.concat "+" (List.map pprint_rule_elem r.rule_rhs))
                       ^ (String.concat "+" (List.map pprint_param_decl r.rule_temps))
                         ^ "EOR\n"

let pprint_non_term_rules a = String.concat "+" (List.map print_rule a);;

let pprint_decl_non_term a =
  Printf.sprintf "non-term-decl: %s\n" a.non_term_name.pelem
  ^ pprint_non_term_varname a.non_term_varname
  ^ pprint_non_term_inh_attrs a.non_term_inh_attrs
  ^ pprint_non_term_syn_attrs a.non_term_syn_attrs
  ^ pprint_non_term_rules a.non_term_rules
;;
(* let pprint_format_decl_desc = function
 *   | Decl_use x -> pprint_decl_use x
 *   | Decl_non_term y -> pprint_decl_non_term y
 *   | _ -> "other type" *)

(* END *)


let pprint_ident fmt f = Fmt.string fmt f.pelem;;

let pprint_format_name fmt f = Fmt.string fmt "format_name: "; pprint_ident fmt f.format_name;;

let pprint_format_loc fmt f = pf fmt "format_loc:";;

let pprint_format_decl_desc fmt f = pf fmt "placeholder_decL-desc"

let pprint_format_decl fmt format_decls= Fmt.string fmt "format_decl: "; Fmt.braces (pprint_format_decl_desc ++ Fmt.semi ++ pprint_format_loc) fmt format_decls;;

let pprint_format_decls_list fmt f = Fmt.string fmt "format_decls_list: "; brackets (Fmt.list ~sep:comma pprint_format_decl) fmt f.format_decls

let pprint_decl_format = Fmt.braces (pprint_format_name ++ comma ++ pprint_format_decls_list ++ comma ++ pprint_format_loc);;

let pprint_top_decl fmt = function
    | Decl_use x -> pf fmt "decl use"
    | Decl_type y -> pf fmt "decl type"
    | Decl_fun z -> pf fmt "decl fun"
    | Decl_format a -> Fmt.string fmt " decl_format: " ; pprint_decl_format fmt a;;

let print_ast fmt ast = Fmt.string fmt " ast: "; Fmt.brackets (Fmt.list pprint_top_decl) fmt ast.decls;;

let print_ast ast = print_ast Fmt.stdout ast
