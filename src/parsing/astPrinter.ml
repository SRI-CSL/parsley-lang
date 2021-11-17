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

let pp_string    = pp_print_string !ppf
let pp_open_box  = pp_open_box !ppf
let pp_open_vbox = pp_open_vbox !ppf
let pp_close_box = pp_close_box !ppf
let pp_break     = pp_print_break !ppf
let pp_flush     = pp_print_flush !ppf
let pp_newline   = pp_print_newline !ppf
let pp_cut       = pp_print_cut !ppf


let rec print_list sep printer = function
  | [] -> ()
  | [ e ] ->
      printer e
  | h :: t ->
      printer h;
      pp_string  sep;
      print_list sep printer t

let string_of_constructor (t, c) =
  AstUtils.canonicalize_dcon (Location.value t) (Location.value c)

let str_of_unop = function
  | Uminus -> "-"
  | Not -> "!"
  | Neg_b -> "~"

let str_of_binop = function
  | Lt -> "<" | Gt -> ">" | Lteq -> "<=" | Gteq -> ">=" | Eq -> "=" | Neq -> "!="
  | Plus -> "+" | Plus_s -> "+_s" | Minus -> "-" | Mult -> "*" | Div -> "/"
  | Land -> "&&" | Lor -> "||"
  | And_b -> "&_b" | Or_b -> "|_b"
  | Cons -> "::" | At -> "@"
  | Index -> assert false (* needs special handling by caller *)

let string_of_bitvector v =
  "0b" ^ (String.concat "" (List.map (fun b ->
                                if b then "1" else "0"
                              ) v))

let string_of_literal l =
  match l with
    | PL_unit        -> "()"
    | PL_string s    -> Printf.sprintf "\"%s\"" s
    | PL_int i       -> string_of_int i
    | PL_bool b      -> if b then "bool::True" else "bool::False"
    | PL_bit b       -> if b then "bit::One"   else "bit::Zero"
    | PL_bitvector v -> string_of_bitvector v

let rec print_kind = function
  | KStar ->
      pp_string "*"
  | KNat ->
      pp_string "Nat"
  | KArrow (KStar, k2) ->
      pp_string "* -> ";
      print_kind k2
  | KArrow (KNat, k2) ->
      pp_string "Nat -> ";
      print_kind k2
  | KArrow (k1, k2) ->
      pp_string "(";
      print_kind k1;
      pp_string ") -> ";
      print_kind k2

let rec print_type_expr ?paren te =
  match te.type_expr with
    | TE_tvar t ->
        pp_string (Location.value t)
    | TE_tapp ({type_expr = TE_tvar t; _}, args)
         when Location.value t = "->" ->
        if paren <> None then pp_string "(";
        print_list " -> " print_type_expr args;
        if paren <> None then pp_string ")";
    | TE_tapp (con, args) ->
        if paren <> None then pp_string "(";
        print_type_expr con;
        if List.length args > 0 then begin
            pp_string "(";
            print_list ", " print_type_expr args;
            pp_string ")"
          end;
        if paren <> None then pp_string ")"

let print_type_rep tr =
  match tr.type_rep with
    | TR_variant cons ->
        let first = ref true in
        let print_data_cons dc =
          if !first
          then (pp_string "  ";
                first := false)
          else (pp_break  0 0;
                pp_string "| ");
          match dc with
            | id, Some te ->
                pp_string (Location.value id);
                pp_string " of ";
                print_type_expr te
            | id, None ->
                pp_string (Location.value id)
        in
        pp_open_vbox 0;
        List.iter (fun dc ->
            print_data_cons dc
          ) cons;
        pp_close_box ()
    | TR_record fields ->
        pp_string "{";
        print_list ", " (fun (l, t) ->
            pp_string (Location.value l);
            pp_string ": ";
            print_type_expr t
          )
          fields;
        pp_string "}"
    | TR_bitfield fields ->
        pp_string "{";
        print_list ", " (fun (f, (n,m)) ->
            pp_string (Location.value f);
            pp_string ": ";
            let n = Location.value n in
            let m = Location.value m in
            let r = Printf.sprintf "%d:%d" n m in
            pp_string  r
          )
          fields;
        pp_string "}"
    | TR_defn t ->
        print_type_expr t

let print_type_decl td =
  pp_open_box  0;
  pp_string "type ";
  pp_string (Location.value td.type_decl_ident);
  if List.length td.type_decl_tvars > 0 then begin
      pp_string " (";
      print_list ", " (fun e ->
          pp_string (Location.value e)
        ) td.type_decl_tvars;
      pp_string ")";
    end;
  pp_string " : ";
  print_kind td.type_decl_kind;
  pp_string " = ";
  print_type_rep td.type_decl_body;
  pp_close_box ();
  pp_cut ();
  pp_newline ()

let rec print_pattern auxp p =
  match p.pattern with
    | P_wildcard ->
        pp_string "_"
    | P_var id ->
        pp_string (var_name id);
        pp_string (auxp p.pattern_aux)
    | P_literal l ->
        pp_string (string_of_literal l)
    | P_variant (c, ps) ->
        pp_string (string_of_constructor c);
        if List.length ps > 0 then begin
            pp_string "(";
            print_list ", " (print_pattern auxp) ps;
            pp_string ")"
          end

let rec sprint_pattern p =
  match p.pattern with
    | P_wildcard | P_var _ -> "_"
    | P_literal PL_unit -> "()"
    | P_literal (PL_string s) -> "\"" ^ s ^ "\""
    | P_literal (PL_int i) -> Printf.sprintf "%d" i
    | P_literal (PL_bool b) -> if b then "bool::True()" else "bool::False()"
    | P_literal (PL_bit b) -> if b then "bit::One()" else "bit::Zero()"
    | P_literal (PL_bitvector bv) ->
        "0b" ^
          (String.concat "" (List.map (fun b -> if b then "1" else "0") bv))
    | P_variant (c, ps) ->
        let con = string_of_constructor c in
        if List.length ps = 0 then con
        else let args = List.map sprint_pattern ps in
             Printf.sprintf "%s(%s)" con (String.concat ", " args)

let rec print_clause auxp (p, e) =
  pp_string "| ";
  print_pattern auxp p;
  pp_string " -> ";
  print_expr auxp e

and print_clauses auxp = function
  | [] -> ()
  | [c] -> print_clause auxp c
  | c :: t ->
      print_clause auxp c;
      pp_break  1 0;
      print_clauses auxp t

and print_expr auxp e =
  match e.expr with
    | E_var i ->
        pp_string (var_name i);
        pp_string (auxp e.expr_aux)
    | E_constr (c, args) ->
        pp_string (string_of_constructor c);
        pp_string "(";
        print_list ", " (print_expr auxp) args;
        pp_string ")"
    | E_record fields ->
        pp_string "{";
        print_list ", " (fun (f, e) ->
            pp_string (Location.value f);
            pp_string ": ";
            print_expr auxp e;
          ) fields;
        pp_string "}"
    | E_apply (f, args) ->
        pp_string "(";
        print_expr auxp f;
        pp_string " ";
        print_list " " (print_expr auxp) args;
        pp_string ")"
    | E_unop (u, e) ->
        pp_string (str_of_unop u);
        pp_string "(";
        print_expr auxp e;
        pp_string ")"
    | E_binop (Index, l, r) ->
        print_expr auxp l;
        pp_string "[";
        print_expr auxp r;
        pp_string "]"
    | E_binop (b, l, r) ->
        pp_string "(";
        print_expr auxp l;
        pp_string (Printf.sprintf " %s " (str_of_binop b));
        print_expr auxp r;
        pp_string ")"
    | E_recop (r, rop, e) ->
        let r = Printf.sprintf "%s->%s"
                  (Location.value r) (Location.value rop) in
        pp_string  r;
        pp_string "(";
        print_expr auxp e;
        pp_string ")"
    | E_bitrange (e, n, m) ->
        print_expr auxp e;
        pp_string "[[";
        pp_string (string_of_int n);
        pp_string ":";
        pp_string (string_of_int m);
        pp_string "]]"
    | E_literal l ->
        pp_string (string_of_literal l)
    | E_field (e, f) ->
        let complex = (match e.expr with E_var _ -> false | _ -> true) in
        if complex then pp_string "(";
        print_expr auxp e;
        if complex then pp_string ")";
        pp_string ".";
        pp_string (Location.value f)
    | E_mod_member (m, i) ->
        pp_string "(";
        pp_string
          (Printf.sprintf "%s.%s" (Location.value m) (Location.value i));
        pp_string ": ";
        pp_string (auxp e.expr_aux);
        pp_string ") "
    | E_match (e, c) ->
        pp_string "(";
        print_expr auxp e;
        pp_string " ~~ ";
        pp_string (string_of_constructor c);
        pp_string ")"
    | E_case (d, clauses) ->
        pp_open_vbox  2;
        pp_string "(case ";
        print_expr auxp d;
        pp_string " of ";
        pp_break  0 0;
        print_clauses auxp clauses;
        pp_close_box ();
        pp_string ")"
    | E_let (p, e, b) ->
        pp_string "let ";
        print_pattern auxp p;
        pp_string " = ";
        print_expr auxp e;
        pp_string " in ";
        print_expr auxp b
    | E_cast (e, t) ->
        pp_string "(";
        print_expr auxp e;
        pp_string " : ";
        print_type_expr t;
        pp_string ")"

let print_param_decl (pm, ty) =
  pp_string (var_name pm);
  pp_string ": ";
  print_type_expr ty

let print_attr_decl auxp (pm, ty, ex) =
  pp_string (Location.value pm);
  pp_string ": ";
  print_type_expr ty;
  (match ex with
     | None -> ()
     | Some e ->
         pp_string " := ";
         print_expr auxp e)

let print_temp_decl auxp (pm, ty, e) =
  pp_string (var_name pm);
  pp_string ": ";
  print_type_expr ty;
  pp_string " := ";
  print_expr auxp e

let print_fun_defn auxp fd =
  pp_open_vbox  0;
  pp_open_box  0;
  pp_string (if fd.fun_defn_recursive
             then "recfun "
             else "fun ");
  pp_string (var_name fd.fun_defn_ident);
  if List.length fd.fun_defn_tvars > 0 then begin
      pp_string " <";
      print_list ", " (fun e ->
          pp_string (Location.value e)
        ) fd.fun_defn_tvars;
      pp_string ">"
    end;
  pp_string "(";
  print_list ", " print_param_decl fd.fun_defn_params;
  pp_string ")";
  pp_string " -> ";
  print_type_expr fd.fun_defn_res_type;
  pp_string " = {";
  pp_close_box ();
  pp_cut ();
  pp_open_box  2;
  pp_break  2 0;
  print_expr auxp fd.fun_defn_body;
  pp_close_box ();
  pp_newline ();
  pp_string "}"

let print_attributes auxp at op cl =
  match at with
    | ALT_type t ->
        pp_string  op;
        pp_string (Printf.sprintf " %s " (Location.value t));
        pp_string  cl
    | ALT_decls pd ->
        if List.length pd > 0
        then (
          pp_string  op;
          print_list ", " (print_attr_decl auxp) pd;
          pp_string  cl
        )

let rec print_literal_set ls =
  match ls.literal_set with
    | LS_type id ->
        pp_string (Location.value id)
    | LS_set l ->
        print_list " | " (fun e ->
            pp_string (Printf.sprintf "\"%s\"" (Location.value e))
          ) l
    | LS_diff (l, r) ->
        pp_string "(";
        print_literal_set l;
        pp_string " \ ";
        print_literal_set r;
        pp_string ")"
    | LS_range (b, e) ->
        pp_string "(";
        pp_string (Printf.sprintf "\"%s\"" (Location.value b));
        pp_string " .. ";
        pp_string (Printf.sprintf "\"%s\"" (Location.value e));
        pp_string ")"

let rec print_regexp auxp re =
  match re.regexp with
    | RX_empty ->
        pp_string "$epsilon"
    | RX_literals ls ->
        pp_string "[";
        print_literal_set ls;
        pp_string "]"
    | RX_wildcard ->
        pp_string "#"
    | RX_type t ->
        pp_string (Location.value t)
    | RX_star (re, bound) ->
        (match bound with
           | Some e ->
               pp_string "(";
               print_regexp auxp re;
               pp_string ") ^ (";
               print_expr auxp e;
               pp_string ")"
           | None ->
               pp_string "(";
               print_regexp auxp re;
               pp_string ")*"
        )
    | RX_opt re ->
        pp_string "(";
        print_regexp auxp re;
        pp_string ")?"
    | RX_choice res ->
        pp_string "(";
        print_list " | " (print_regexp auxp) res;
        pp_string ")"
    | RX_seq res ->
        pp_string "(";
        print_list " " (print_regexp auxp) res;
        pp_string ")"

let rec print_clause auxp (p, s) =
  pp_string "| ";
  print_pattern auxp p;
  pp_string " -> ";
  pp_cut ();
  pp_open_vbox  2;
  pp_string " { ";
  print_list "; " (print_stmt auxp) s;
  pp_string " }";
  pp_close_box ()

and print_clauses auxp = function
  | [] -> ()
  | [c] -> print_clause auxp c
  | c :: t ->
      print_clause auxp c;
      pp_break  1 0;
      print_clauses auxp t

and print_stmt auxp s =
  match s.stmt with
    | S_assign (l, r) ->
        print_expr auxp l;
        pp_string " := ";
        print_expr auxp r
    | S_let (p, e, s) ->
        pp_string "let ";
        print_pattern auxp p;
        pp_string " = ";
        print_expr auxp e;
        pp_string " in ";
        pp_cut ();
        pp_open_vbox  2;
        pp_string " { ";
        print_list "; " (print_stmt auxp) s;
        pp_string " }";
        pp_close_box ()
    | S_case (d, clauses) ->
        pp_open_vbox  2;
        pp_string "(case ";
        print_expr auxp d;
        pp_string " of ";
        pp_break  0 0;
        print_clauses auxp clauses;
        pp_close_box ();
        pp_string ")"

let print_action auxp a =
  let (stmts, e_opt) = a.action_stmts in
  let rec print = function
    | []  -> ()
    | [s] -> print_stmt auxp s
    | s :: t ->
        print_stmt auxp s;
        pp_string ";";
        pp_cut ();
        print t in
  pp_cut ();
  pp_open_vbox  2;
  pp_string "{ ";
  print stmts;
  (match e_opt with
     | None -> ()
     | Some e ->
         pp_string ";;";
         pp_cut ();
         print_expr auxp e);
  pp_string " }";
  pp_close_box ()

let rec print_rule_elem auxp rl =
  match rl.rule_elem with
    | RE_regexp re ->
        pp_string "(#";
        print_regexp auxp re;
        pp_string "#) "
    | RE_epsilon ->
        pp_string "$epsilon"
    | RE_non_term (nt, attr_opt) ->
        pp_string (Location.value nt);
        (match attr_opt with
           | Some attrs ->
               pp_string "<";
               print_list ", " (fun (k, v) ->
                   pp_string (Location.value k);
                   pp_string " = ";
                   print_expr auxp v
                 ) attrs;
               pp_string ">";
           | None -> ()
        )
    | RE_bitvector w ->
        pp_string "Bitvector<";
        pp_string (string_of_int (Location.value w));
        pp_string ">"
    | RE_align w ->
        pp_string "$align<";
        pp_string (string_of_int (Location.value w));
        pp_string ">"
    | RE_pad (w, bv) ->
        pp_string "$pad<";
        pp_string (string_of_int (Location.value w));
        pp_string ",";
        pp_string (string_of_bitvector bv);
        pp_string ">"
    | RE_bitfield bf ->
        pp_string "$bitfield(";
        pp_string (Location.value bf);
        pp_string ">"
    | RE_constraint c ->
        pp_cut ();
        pp_string "[";
        print_expr auxp c;
        pp_string "]";
        pp_cut ();
    | RE_action a ->
        print_action auxp a
    | RE_named (id, rl) ->
        pp_string (var_name id);
        pp_string (auxp rl.rule_elem_aux);
        pp_string "= ";
        print_rule_elem auxp rl
    | RE_seq rls | RE_seq_flat rls ->
        pp_string "(";
        print_list " " (print_rule_elem auxp) rls;
        pp_string ")"
    | RE_choice rls ->
        print_list " | " (print_rule_elem auxp) rls
    | RE_star (r, bound) ->
        (match bound with
           | Some e ->
               pp_string "(";
               print_rule_elem auxp r;
               pp_string ") ^ (";
               print_expr auxp e;
               pp_string ")"
           | None ->
               pp_string "(";
               print_rule_elem auxp r;
               pp_string ")*"
        )
    | RE_opt r ->
        pp_string "(";
        print_rule_elem auxp r;
        pp_string ")?*"
    | RE_set_view (e) ->
        pp_string "@^[";
        print_expr auxp e;
        pp_string "]"
    | RE_at_pos (e, rl) ->
        pp_string "@(";
        print_expr auxp e;
        pp_string ", ";
        print_rule_elem auxp rl;
        pp_string ")"
    | RE_at_view (e, rl) ->
        pp_string "@[";
        print_expr auxp e;
        pp_string ", ";
        print_rule_elem auxp rl;
        pp_string "]"
    | RE_map_views (e, rl) ->
        pp_string "@#[";
        print_expr auxp e;
        pp_string ", ";
        print_rule_elem auxp rl;
        pp_string "]"

let print_rule auxp rl =
  if List.length rl.rule_temps > 0 then begin
      pp_string "(|";
      print_list ", " (print_temp_decl auxp) rl.rule_temps;
      pp_string "|)";
      pp_cut ();
    end;
  pp_open_box  2;
  let rec print = function
    | [] -> ()
    | [r] -> print_rule_elem auxp r
    | r :: t -> begin
        print_rule_elem auxp r;
        pp_break  2 0;
        print t
      end in
  print rl.rule_rhs;
  pp_close_box ();
  pp_cut ()

let print_nterm_defn auxp nd =
  pp_open_box  0;
  pp_string (Location.value nd.non_term_name);
  (match nd.non_term_varname with
     | Some v ->
         pp_string " ";
         pp_string (var_name v)
     | None -> ());
  if List.length nd.non_term_inh_attrs > 0
  then print_list ", " print_param_decl nd.non_term_inh_attrs;
  pp_break  1 2;
  print_attributes auxp nd.non_term_syn_attrs "{" "}";
  pp_string " :=";
  pp_close_box ();
  pp_cut ();
  pp_open_vbox  2;
  pp_string "  ";
  let rec print = function
    | [] -> ()
    | [h] -> print_rule auxp h
    | h :: t ->
        print_rule auxp h;
        pp_string ";";
        pp_cut ();
        print t
  in print nd.non_term_rules;
  pp_close_box ();
  pp_string ";;"

let print_format auxp f =
  pp_open_vbox  2;
  pp_string "format {";
  pp_cut ();
  List.iter (fun fd ->
      print_nterm_defn auxp fd.format_decl;
      pp_cut ();
      pp_cut ()
    ) f.format_decls;
  pp_close_box ();
  pp_cut ();
  pp_string "}"

let print_const auxp c =
  pp_open_box  0;
  pp_string "const ";
  pp_string (var_name c.const_defn_ident);
  pp_string " : ";
  print_type_expr c.const_defn_type;
  pp_string " = ";
  print_expr auxp c.const_defn_val;
  pp_close_box ();
  pp_cut ();
  pp_newline ()

let print_decl auxp d =
  match d with
    | Decl_const c ->
        print_const auxp c
    | Decl_types (typs, _) ->
        List.iter print_type_decl typs
    | Decl_fun fd ->
        print_fun_defn auxp fd
    | Decl_format f ->
        print_format auxp f

let rec print_decls auxp = function
  | [] -> ()
  | h :: t -> begin
      pp_open_box  0;
      print_decl auxp h;
      pp_newline ();
      pp_newline ();
      pp_close_box ();
      print_decls auxp t
    end

let print_spec auxp spec =
  print_decls auxp spec.decls;
  pp_flush ()

let print_parsed_spec spec =
  let auxp () = "" in
  print_spec auxp spec

let print_typed_spec type_printer spec =
  let auxp t =
    let s = type_printer t in
    Printf.sprintf " (: %s) " s in
  print_spec auxp spec
