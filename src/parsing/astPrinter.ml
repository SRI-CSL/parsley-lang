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

open Ast
open Format

let ppf = ref std_formatter

let print_flush () =
  pp_print_flush !ppf ()

let rec print_list sep printer = function
  | [] -> ()
  | [ e ] ->
      printer e
  | h :: t ->
      printer h;
      pp_print_string !ppf sep;
      print_list sep printer t

let rec print_kind = function
  | KStar ->
      pp_print_string !ppf "*"
  | KArrow (KStar, k2) ->
      pp_print_string !ppf "* -> ";
      print_kind k2
  | KArrow (k1, k2) ->
      pp_print_string !ppf "(";
      print_kind k1;
      pp_print_string !ppf ") -> ";
      print_kind k2

let rec print_type_expr ?paren te =
  match te.type_expr with
    | TE_tvar t ->
        pp_print_string !ppf (Location.value t)
    | TE_tapp ({type_expr = TE_tvar t; _}, args)
         when Location.value t = "->" ->
        if paren <> None then pp_print_string !ppf "(";
        print_list " -> " print_type_expr args;
        if paren <> None then pp_print_string !ppf ")";
    | TE_tapp (con, args) ->
        if paren <> None then pp_print_string !ppf "(";
        print_type_expr con;
        if List.length args > 0 then begin
            pp_print_string !ppf "(";
            print_list ", " print_type_expr args;
            pp_print_string !ppf ")"
          end;
        if paren <> None then pp_print_string !ppf ")"

let print_type_rep tr =
  match tr.type_rep with
    | TR_variant cons ->
        let first = ref true in
        let print_data_cons dc =
          if !first
          then (pp_print_string !ppf "  ";
                first := false)
          else (pp_print_break !ppf 0 0;
                pp_print_string !ppf "| ");
          match dc with
            | id, Some te ->
                pp_print_string !ppf (Location.value id);
                pp_print_string !ppf " of ";
                print_type_expr te
            | id, None ->
                pp_print_string !ppf (Location.value id)
        in
        pp_open_vbox !ppf 0;
        List.iter (fun dc ->
            print_data_cons dc
          ) cons;
        pp_close_box !ppf ()
    | TR_record fields ->
        pp_print_string !ppf "{";
        print_list ", " (fun (l, t) ->
            pp_print_string !ppf (Location.value l);
            pp_print_string !ppf ": ";
            print_type_expr t
          )
          fields;
        pp_print_string !ppf "}"

    | TR_defn t ->
        print_type_expr t

let print_type_decl td =
  pp_open_box !ppf 0;
  pp_print_string !ppf "type ";
  pp_print_string !ppf (Location.value td.type_decl_ident);
  if List.length td.type_decl_tvars > 0 then begin
      pp_print_string !ppf " (";
      print_list ", " (fun e ->
          pp_print_string !ppf (Location.value e)
        ) td.type_decl_tvars;
      pp_print_string !ppf ")";
    end;
  pp_print_string !ppf " : ";
  print_kind td.type_decl_kind;
  pp_print_string !ppf " = ";
  print_type_rep td.type_decl_body;
  pp_close_box !ppf ();
  pp_print_cut !ppf ();
  pp_print_newline !ppf ()

let rec print_pattern auxp p =
  match p.pattern with
    | P_wildcard ->
        pp_print_string !ppf "_"
    | P_var id ->
        pp_print_string !ppf (var_name id);
        pp_print_string !ppf (auxp p.pattern_aux)
    | P_literal PL_unit ->
        pp_print_string !ppf "()"
    | P_literal (PL_string l) ->
        pp_print_string !ppf (Printf.sprintf "\"%s\"" l)
    | P_literal (PL_int l) ->
        pp_print_string !ppf (string_of_int l)
    | P_literal (PL_bool b) ->
        pp_print_string !ppf (if b then "true" else "false")
    | P_variant ((t,c), ps) ->
        pp_print_string !ppf
          (AstUtils.canonicalize_dcon
             (Location.value t) (Location.value c));
        if List.length ps > 0 then begin
            pp_print_string !ppf "(";
            print_list ", " (print_pattern auxp) ps;
            pp_print_string !ppf ")"
          end

let rec sprint_pattern p =
  match p.pattern with
    | P_wildcard | P_var _ -> "_"
    | P_literal PL_unit -> "()"
    | P_literal (PL_string s) -> "\"" ^ s ^ "\""
    | P_literal (PL_int i) -> Printf.sprintf "%d" i
    | P_literal (PL_bool b) -> if b then "bool::True()" else "bool::False()"
    | P_variant ((t, c), ps) ->
        let con = AstUtils.canonicalize_dcon
                    (Location.value t) (Location.value c) in
        if List.length ps = 0 then con
        else let args = List.map sprint_pattern ps in
             Printf.sprintf "%s(%s)" con (String.concat ", " args)

let str_of_unop = function
  | Uminus -> "-"
  | Not -> "!"

let str_of_binop = function
  | Lt -> "<" | Gt -> ">" | Lteq -> "<=" | Gteq -> ">=" | Eq -> "=" | Neq -> "!="
  | Plus -> "+" | Plus_s -> "+_s" | Minus -> "-" | Mult -> "*" | Div -> "/"
  | Land -> "&&" | Lor -> "||"
  | Cons -> "::" | At -> "@"
  | Index -> assert false (* needs special handling by caller *)

let rec print_clause auxp (p, e) =
  pp_print_string !ppf "| ";
  print_pattern auxp p;
  pp_print_string !ppf " -> ";
  print_expr auxp e

and print_clauses auxp = function
  | [] -> ()
  | [c] -> print_clause auxp c
  | c :: t ->
      print_clause auxp c;
      pp_print_break !ppf 1 0;
      print_clauses auxp t

and print_expr auxp e =
  match e.expr with
    | E_var i ->
        pp_print_string !ppf (var_name i);
        pp_print_string !ppf (auxp e.expr_aux)
    | E_constr ((t, c), args) ->
        pp_print_string !ppf
          (AstUtils.canonicalize_dcon
             (Location.value t) (Location.value c));
        if List.length args > 0 then begin
            pp_print_string !ppf "(";
            print_list ", " (print_expr auxp) args;
            pp_print_string !ppf ")";
          end
    | E_record fields ->
        pp_print_string !ppf "{";
        print_list ", " (fun (f, e) ->
            pp_print_string !ppf (Location.value f);
            pp_print_string !ppf ": ";
            print_expr auxp e;
          ) fields;
        pp_print_string !ppf "}"
    | E_apply (f, args) ->
        pp_print_string !ppf "(";
        print_expr auxp f;
        pp_print_string !ppf " ";
        print_list " " (print_expr auxp) args;
        pp_print_string !ppf ")"
    | E_unop (u, e) ->
        pp_print_string !ppf (str_of_unop u);
        pp_print_string !ppf "(";
        print_expr auxp e;
        pp_print_string !ppf ")"
    | E_binop (Index, l, r) ->
        print_expr auxp l;
        pp_print_string !ppf "[";
        print_expr auxp r;
        pp_print_string !ppf "]"
    | E_binop (b, l, r) ->
        pp_print_string !ppf "(";
        print_expr auxp l;
        pp_print_string !ppf (Printf.sprintf " %s " (str_of_binop b));
        print_expr auxp r;
        pp_print_string !ppf ")"
    | E_literal PL_unit ->
        pp_print_string !ppf "()"
    | E_literal (PL_string l) ->
        pp_print_string !ppf (Printf.sprintf "\"%s\"" l)
    | E_literal (PL_int i) ->
        pp_print_string !ppf (string_of_int i)
    | E_literal (PL_bool b) ->
        pp_print_string !ppf (if b then "true" else "false")
    | E_field (e, f) ->
        let complex = (match e.expr with E_var _ -> false | _ -> true) in
        if complex then pp_print_string !ppf "(";
        print_expr auxp e;
        if complex then pp_print_string !ppf ")";
        pp_print_string !ppf ".";
        pp_print_string !ppf (Location.value f)
    | E_mod_member (m, i) ->
        pp_print_string !ppf
          (Printf.sprintf "%s.%s" (Location.value m) (Location.value i))
    | E_match (e, (t, c)) ->
        pp_print_string !ppf "(";
        print_expr auxp e;
        pp_print_string !ppf " ~~ ";
        pp_print_string !ppf
          (AstUtils.canonicalize_dcon
             (Location.value t) (Location.value c));
        pp_print_string !ppf ")"
    | E_case (d, clauses) ->
        pp_open_vbox !ppf 2;
        pp_print_string !ppf "(case ";
        print_expr auxp d;
        pp_print_string !ppf " of ";
        pp_print_break !ppf 0 0;
        print_clauses auxp clauses;
        pp_close_box !ppf ();
        pp_print_string !ppf ")"
    | E_let (p, e, b) ->
        pp_print_string !ppf "let ";
        print_pattern auxp p;
        pp_print_string !ppf " = ";
        print_expr auxp e;
        pp_print_string !ppf " in ";
        print_expr auxp b
    | E_cast (e, t) ->
        pp_print_string !ppf "(";
        print_expr auxp e;
        pp_print_string !ppf " : ";
        print_type_expr t;
        pp_print_string !ppf ")"

let print_param_decl (pm, ty) =
  pp_print_string !ppf (var_name pm);
  pp_print_string !ppf ": ";
  print_type_expr ty

let print_attr_decl auxp (pm, ty, ex) =
  pp_print_string !ppf (Location.value pm);
  pp_print_string !ppf ": ";
  print_type_expr ty;
  (match ex with
     | None -> ()
     | Some e ->
         pp_print_string !ppf " := ";
         print_expr auxp e)

let print_temp_decl auxp (pm, ty, e) =
  pp_print_string !ppf (var_name pm);
  pp_print_string !ppf ": ";
  print_type_expr ty;
  pp_print_string !ppf " := ";
  print_expr auxp e

let print_fun_defn auxp fd =
  pp_open_vbox !ppf 0;
  pp_open_box !ppf 0;
  pp_print_string !ppf "fun ";
  pp_print_string !ppf (var_name fd.fun_defn_ident);
  if List.length fd.fun_defn_tvars > 0 then begin
      pp_print_string !ppf " <";
      print_list ", " (fun e ->
          pp_print_string !ppf (Location.value e)
        ) fd.fun_defn_tvars;
      pp_print_string !ppf ">"
    end;
  pp_print_string !ppf "(";
  print_list ", " print_param_decl fd.fun_defn_params;
  pp_print_string !ppf ")";
  pp_print_string !ppf " -> ";
  print_type_expr fd.fun_defn_res_type;
  pp_print_string !ppf " = {";
  pp_close_box !ppf ();
  pp_print_cut !ppf ();
  pp_open_box !ppf 2;
  pp_print_break !ppf 2 0;
  print_expr auxp fd.fun_defn_body;
  pp_close_box !ppf ();
  pp_print_newline !ppf ();
  pp_print_string !ppf "}"

let print_attributes auxp at op cl =
  match at with
    | ALT_type t ->
        pp_print_string !ppf op;
        pp_print_string !ppf (Printf.sprintf " %s " (Location.value t));
        pp_print_string !ppf cl
    | ALT_decls pd ->
        if List.length pd > 0
        then (
          pp_print_string !ppf op;
          print_list ", " (print_attr_decl auxp) pd;
          pp_print_string !ppf cl
        )

let rec print_literal_set ls =
  match ls.literal_set with
    | LS_type id ->
        pp_print_string !ppf (Location.value id)
    | LS_set l ->
        print_list " | " (fun e ->
            pp_print_string !ppf (Printf.sprintf "\"%s\"" (Location.value e))
          ) l
    | LS_diff (l, r) ->
        pp_print_string !ppf "(";
        print_literal_set l;
        pp_print_string !ppf " \ ";
        print_literal_set r;
        pp_print_string !ppf ")"
    | LS_range (b, e) ->
        pp_print_string !ppf "(";
        pp_print_string !ppf (Printf.sprintf "\"%s\"" (Location.value b));
        pp_print_string !ppf " .. ";
        pp_print_string !ppf (Printf.sprintf "\"%s\"" (Location.value e));
        pp_print_string !ppf ")"

let rec print_regexp auxp re =
  match re.regexp with
    | RX_literals ls ->
        pp_print_string !ppf "[";
        print_literal_set ls;
        pp_print_string !ppf "]"
    | RX_wildcard ->
        pp_print_string !ppf "#"
    | RX_type t ->
        pp_print_string !ppf (Location.value t)
    | RX_star (re, bound) ->
        (match bound with
           | Some e ->
               pp_print_string !ppf "(";
               print_regexp auxp re;
               pp_print_string !ppf ") ^ (";
               print_expr auxp e;
               pp_print_string !ppf ")"
           | None ->
               pp_print_string !ppf "(";
               print_regexp auxp re;
               pp_print_string !ppf ")*"
        )
    | RX_opt re ->
        pp_print_string !ppf "(";
        print_regexp auxp re;
        pp_print_string !ppf ")?"
    | RX_choice res ->
        pp_print_string !ppf "(";
        print_list " | " (print_regexp auxp) res;
        pp_print_string !ppf ")"
    | RX_seq res ->
        pp_print_string !ppf "(";
        print_list " " (print_regexp auxp) res;
        pp_print_string !ppf ")"

let rec print_clause auxp (p, s) =
  pp_print_string !ppf "| ";
  print_pattern auxp p;
  pp_print_string !ppf " -> ";
  pp_print_cut !ppf ();
  pp_open_vbox !ppf 2;
  pp_print_string !ppf " { ";
  print_list "; " (print_stmt auxp) s;
  pp_print_string !ppf " }";
  pp_close_box !ppf ()

and print_clauses auxp = function
  | [] -> ()
  | [c] -> print_clause auxp c
  | c :: t ->
      print_clause auxp c;
      pp_print_break !ppf 1 0;
      print_clauses auxp t

and print_stmt auxp s =
  match s.stmt with
    | S_assign (l, r) ->
        print_expr auxp l;
        pp_print_string !ppf " := ";
        print_expr auxp r
    | S_let (p, e, s) ->
        pp_print_string !ppf "let ";
        print_pattern auxp p;
        pp_print_string !ppf " = ";
        print_expr auxp e;
        pp_print_string !ppf " in ";
        pp_print_cut !ppf ();
        pp_open_vbox !ppf 2;
        pp_print_string !ppf " { ";
        print_list "; " (print_stmt auxp) s;
        pp_print_string !ppf " }";
        pp_close_box !ppf ()
    | S_case (d, clauses) ->
        pp_open_vbox !ppf 2;
        pp_print_string !ppf "(case ";
        print_expr auxp d;
        pp_print_string !ppf " of ";
        pp_print_break !ppf 0 0;
        print_clauses auxp clauses;
        pp_close_box !ppf ();
        pp_print_string !ppf ")"

let print_action auxp a =
  let (stmts, e_opt) = a.action_stmts in
  let rec print = function
    | []  -> ()
    | [s] -> print_stmt auxp s
    | s :: t ->
        print_stmt auxp s;
        pp_print_string !ppf ";";
        pp_print_cut !ppf ();
        print t in
  pp_print_cut !ppf ();
  pp_open_vbox !ppf 2;
  pp_print_string !ppf "{ ";
  print stmts;
  (match e_opt with
     | None -> ()
     | Some e ->
         pp_print_string !ppf ";;";
         pp_print_cut !ppf ();
         print_expr auxp e);
  pp_print_string !ppf " }";
  pp_close_box !ppf ()

let rec print_rule_elem auxp rl =
  match rl.rule_elem with
    | RE_regexp re ->
        pp_print_string !ppf "(#";
        print_regexp auxp re;
        pp_print_string !ppf "#) "
    | RE_epsilon ->
        pp_print_string !ppf "$epsilon"
    | RE_non_term (nt, attr_opt) ->
        pp_print_string !ppf (Location.value nt);
        (match attr_opt with
           | Some attrs ->
               pp_print_string !ppf "<";
               print_list ", " (fun (k, v) ->
                   pp_print_string !ppf (Location.value k);
                   pp_print_string !ppf " = ";
                   print_expr auxp v
                 ) attrs;
               pp_print_string !ppf ">";
           | None -> ()
        )
    | RE_constraint c ->
        pp_print_cut !ppf ();
        pp_print_string !ppf "[";
        print_expr auxp c;
        pp_print_string !ppf "]";
        pp_print_cut !ppf ();
    | RE_action a ->
        print_action auxp a
    | RE_named (id, rl) ->
        pp_print_string !ppf (var_name id);
        pp_print_string !ppf (auxp rl.rule_elem_aux);
        pp_print_string !ppf "=";
        print_rule_elem auxp rl
    | RE_seq rls ->
        pp_print_string !ppf "(";
        print_list " " (print_rule_elem auxp) rls;
        pp_print_string !ppf ")"
    | RE_choice rls ->
        print_list " | " (print_rule_elem auxp) rls
    | RE_star (r, bound) ->
        (match bound with
           | Some e ->
               pp_print_string !ppf "(";
               print_rule_elem auxp r;
               pp_print_string !ppf ") ^ (";
               print_expr auxp e;
               pp_print_string !ppf ")"
           | None ->
               pp_print_string !ppf "(";
               print_rule_elem auxp r;
               pp_print_string !ppf ")*"
        )
    | RE_opt r ->
        pp_print_string !ppf "(";
        print_rule_elem auxp r;
        pp_print_string !ppf ")?*"
    | RE_at_pos (e, rl) ->
        pp_print_string !ppf "@(";
        print_expr auxp e;
        pp_print_string !ppf ", ";
        print_rule_elem auxp rl;
        pp_print_string !ppf ")"
    | RE_at_buf (e, rl) ->
        pp_print_string !ppf "@[";
        print_expr auxp e;
        pp_print_string !ppf ", ";
        print_rule_elem auxp rl;
        pp_print_string !ppf "]"
    | RE_map_bufs (e, rl) ->
        pp_print_string !ppf "@#[";
        print_expr auxp e;
        pp_print_string !ppf ", ";
        print_rule_elem auxp rl;
        pp_print_string !ppf "]"

let print_rule auxp rl =
  if List.length rl.rule_temps > 0 then begin
      pp_print_string !ppf "(|";
      print_list ", " (print_temp_decl auxp) rl.rule_temps;
      pp_print_string !ppf "|)";
      pp_print_cut !ppf ();
    end;
  pp_open_box !ppf 2;
  let rec print = function
    | [] -> ()
    | [r] -> print_rule_elem auxp r
    | r :: t -> begin
        print_rule_elem auxp r;
        pp_print_break !ppf 2 0;
        print t
      end in
  print rl.rule_rhs;
  pp_close_box !ppf ();
  pp_print_cut !ppf ()

let print_nterm_defn auxp nd =
  pp_open_box !ppf 0;
  pp_print_string !ppf (Location.value nd.non_term_name);
  (match nd.non_term_varname with
     | Some v ->
         pp_print_string !ppf " ";
         pp_print_string !ppf (var_name v)
     | None -> ());
  if List.length nd.non_term_inh_attrs > 0
  then print_list ", " print_param_decl nd.non_term_inh_attrs;
  pp_print_break !ppf 1 2;
  print_attributes auxp nd.non_term_syn_attrs "{" "}";
  pp_print_string !ppf " :=";
  pp_close_box !ppf ();
  pp_print_cut !ppf ();
  pp_open_vbox !ppf 2;
  pp_print_string !ppf "  ";
  let rec print = function
    | [] -> ()
    | [h] -> print_rule auxp h
    | h :: t ->
        print_rule auxp h;
        pp_print_string !ppf ";";
        pp_print_cut !ppf ();
        print t
  in print nd.non_term_rules;
  pp_close_box !ppf ();
  pp_print_string !ppf ";;"

let print_format auxp f =
  pp_open_vbox !ppf 2;
  pp_print_string !ppf "format {";
  pp_print_cut !ppf ();
  List.iter (fun fd ->
      print_nterm_defn auxp fd.format_decl;
      pp_print_cut !ppf ();
      pp_print_cut !ppf ()
    ) f.format_decls;
  pp_close_box !ppf ();
  pp_print_cut !ppf ();
  pp_print_string !ppf "}"

let print_decl auxp d =
  match d with
    | Decl_types (typs, _) ->
        List.iter print_type_decl typs
    | Decl_fun fd ->
        print_fun_defn auxp fd
    | Decl_format f ->
        print_format auxp f

let rec print_decls auxp = function
  | [] -> ()
  | h :: t -> begin
      pp_open_box !ppf 0;
      print_decl auxp h;
      pp_print_newline !ppf ();
      pp_print_newline !ppf ();
      pp_close_box !ppf ();
      print_decls auxp t
    end

let print_spec auxp spec =
  print_decls auxp spec.decls;
  print_flush ()

let print_parsed_spec spec =
  let auxp () = "" in
  print_spec auxp spec

let print_typed_spec type_printer spec =
  let auxp t =
    let s = type_printer t in
    Printf.sprintf " (: %s) " s in
  print_spec auxp spec