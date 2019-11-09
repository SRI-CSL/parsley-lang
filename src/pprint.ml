open Fmt
open Location
open Ast
open Stdlib

let pprint_ploc fmt l =
  let x, y, z = get_pos_info l.loc_start
  in pf fmt "Location: \n loc_start_pos: %s %d %d" x y z

let pprint_pelem fmt pelem = "placehilder pelem";;

let pprint_location fmt loc = pprint_ploc fmt loc.ploc

(* START *)
(*
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
*)

let pprint_ident fmt f = string fmt f.pelem;;

let pprint_format_name fmt f =
    pf fmt "format_name: ";
    pprint_ident fmt f.format_name;;

let pprint_loc fmt l = pf fmt "loc: xyz" ;;
let pprint_format_loc fmt f = pprint_loc fmt f.format_loc;;
let pprint_format_decl_loc fmt f = pprint_loc fmt f.format_decl_loc;;
let pprint_format_lob fmt f = pf fmt "format_lob: xyz" ;;

let pprint_non_term_name fmt non_term_defn = pprint_ident fmt non_term_defn.non_term_name

let pprint_non_term_varname fmt non_term_defn =
    match non_term_defn.non_term_varname with
    | Some varname -> pf fmt "varname: "; pprint_ident fmt varname;
    | None -> pf fmt "varname: "; pf fmt "none";;

let pprint_str_location fmt x = pf fmt "placeholder str_loc";;

let pprint_expr fmt x = pf fmt "placeholder_expr";;
let pprint_rule_constraint fmt x = pprint_expr fmt x.expr

let pprint_rule_elem_desc fmt = function
  | RE_literal x -> pprint_str_location fmt x
  | RE_non_term (x, y, z) -> pf fmt "placeholder"
  | RE_named_regex (x, y) -> pf fmt "placeholder"
  | RE_constraint x -> pprint_rule_constraint fmt x
  | RE_action x -> pf fmt "placeholder"
  | RE_choice (x, y) -> pf fmt "placeholder"
  | RE_seq x -> pf fmt "placeholder"
  | RE_star x -> pf fmt "placeholder"
  | RE_plus x -> pf fmt "placeholder"
  | RE_opt x -> pf fmt "placeholder"
  | RE_repeat (x, y)-> pf fmt "placeholder"
  | RE_char_class x -> pf fmt "placeholder"

let pprint_rule_elem_loc fmt rule_elem = pprint_loc fmt rule_elem.rule_elem_loc;;

let pprint_rule_loc fmt rule_loc = pf fmt "rule loc placeholder";;

let pprint_rule_temps fmt x = pf fmt "asdasd";;

let pprint_rule_elem fmt rule_elem = pf fmt "asdsad";; (*brackets ( pprint_rule_loc ++ pprint_rule_temps ++ pprint_rule_elem_desc);;
*)
let pprint_rule fmt rule =
    pf fmt "rule rhs:";
    brackets (list pprint_rule_elem) fmt rule.rule_rhs;;

let pprint_non_term_inh_attrs fmt non_term_defn =
    pf fmt "non_term_rules:";
    brackets (list pprint_rule) fmt non_term_defn.non_term_rules;;

let pprint_param_decl fmt param_decl = pf fmt "skip-param-decl"

let pprint_non_term_inh_attrs fmt non_term_defn =
    pf fmt "non_term_inh_attrs: ";
    brackets (list pprint_param_decl) fmt non_term_defn.non_term_inh_attrs;;

let pprint_non_term_syn_attrs fmt non_term_defn =
    pf fmt "non_term_syn_attrs: ";
    brackets (list pprint_param_decl) fmt non_term_defn.non_term_syn_attrs;;

let pprint_non_term_defn fmt non_term_defn =
    pf fmt "non_term_defn: " ;
    braces (concat ~sep:comma [ pprint_non_term_name; pprint_non_term_varname; pprint_non_term_inh_attrs; pprint_non_term_syn_attrs; ]) fmt non_term_defn;;

let pprint_format_decl_desc fmt f =
    match f.format_decl with
    | Format_decl_non_term x -> pprint_non_term_defn fmt x

let pprint_format_decl fmt format_decl =
    pf fmt "format_decl: ";
    braces (concat ~sep:comma [pprint_format_decl_desc; pprint_format_decl_loc]) fmt format_decl;;

let pprint_format_decls_list fmt f =
    pf fmt "format_decls_list: ";
    brackets (list ~sep:comma pprint_format_decl) fmt f.format_decls

let pprint_decl_format = braces (concat ~sep:comma [pprint_format_name; pprint_format_decls_list; pprint_format_loc]);;

let pprint_top_decl fmt = function
    | Decl_use x -> pf fmt "decl use"
    | Decl_type y -> pf fmt "decl type"
    | Decl_fun z -> pf fmt "decl fun"
    | Decl_format a -> pf fmt " decl_format: " ; pprint_decl_format fmt a;;

let print_ast fmt ast =
    pf fmt " ast: ";
    (brackets (list pprint_top_decl)) fmt ast.decls;;
