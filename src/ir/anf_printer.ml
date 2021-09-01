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
open Anf
open Format

let pp_string    = pp_print_string !AstPrinter.ppf
let pp_open_box  = pp_open_box !AstPrinter.ppf
let pp_open_vbox = pp_open_vbox !AstPrinter.ppf
let pp_close_box = pp_close_box !AstPrinter.ppf
let pp_break     = pp_print_break !AstPrinter.ppf
let pp_flush     = pp_print_flush !AstPrinter.ppf
let pp_newline   = pp_print_newline !AstPrinter.ppf
let pp_cut       = pp_print_cut !AstPrinter.ppf

let string_of_var (v, id) =
  if v <> "" && id = 1
  then v
  else Printf.sprintf "#%s%d" v id

let string_of_occurrence occ =
  if occ = []
  then ""
  else "@" ^ (String.concat "/" (List.map string_of_int occ))

let rec print_av av =
  match av.av with
    | AV_lit l ->
        let s = AstPrinter.string_of_literal l in
        pp_string s
    | AV_var v ->
        pp_string (string_of_var v)
    | AV_constr (c, avs) ->
        pp_string (AstPrinter.string_of_constructor c);
        if List.length avs > 0 then begin
            pp_string "(";
            AstPrinter.print_list ", " print_av avs;
            pp_string ")";
          end
    | AV_record fields ->
        pp_string "{";
        AstPrinter.print_list ", " (fun (f, v) ->
            pp_string (Location.value f);
            pp_string ": ";
            print_av v
          ) fields;
        pp_string "}"
    | AV_mod_member (m, i) ->
        pp_string
          (Printf.sprintf "%s.%s" (Location.value m) (Location.value i))

let print_pat p =
  match p.apat with
    | AP_wildcard ->
        pp_string "_"
    | AP_literal l ->
        pp_string (AstPrinter.string_of_literal l)
    | AP_variant c ->
        pp_string (AstPrinter.string_of_constructor c)

let rec print_clause (p, e) =
  pp_string "| ";
  print_pat p;
  pp_string " -> ";
  print_aexp e

and print_clauses = function
  | [] -> ()
  | [c] -> print_clause c
  | c :: t ->
      print_clause c;
      pp_break 1 0;
      print_clauses t

and print_aexp e =
  match e.aexp with
    | AE_val v ->
        print_av v
    | AE_apply (f, vs) ->
        pp_string "(";
        print_av f;
        pp_string " ";
        AstPrinter.print_list " " print_av vs;
        pp_string ")"
    | AE_unop (op, v) ->
        pp_string (AstPrinter.str_of_unop op);
        pp_string "(";
        print_av v;
        pp_string ")"
    | AE_binop (Index, l, r) ->
        print_av l;
        pp_string "[";
        print_av r;
        pp_string "]"
    | AE_binop (b, l, r) ->
        pp_string "(";
        print_av l;
        let op = Printf.sprintf " %s " (AstPrinter.str_of_binop b) in
        pp_string op;
        print_av r;
        pp_string ")"
    | AE_recop (r, rop, v) ->
        let r = Printf.sprintf "%s->%s"
                  (Location.value r) (Location.value rop) in
        pp_string r;
        pp_string "(";
        print_av v;
        pp_string ")"
    | AE_bitrange (v, n, m) ->
        print_av v;
        pp_string "[[";
        pp_string (string_of_int n);
        pp_string ":";
        pp_string (string_of_int m);
        pp_string "]]"
    | AE_match (v, c) ->
        pp_string "(";
        print_av v;
        pp_string " ~~ ";
        pp_string (AstPrinter.string_of_constructor c);
        pp_string ")"
    | AE_field (v, f) ->
        print_av v;
        pp_string ".";
        pp_string (Location.value f)
    | AE_cast (v, t) ->
        pp_string "(";
        print_av v;
        pp_string " : ";
        AstPrinter.print_type_expr t;
        pp_string ")"
    | AE_case (v, clauses) ->
        pp_open_vbox 2;
        pp_string "(case ";
        pp_string (string_of_var v.v);
        pp_string " of ";
        pp_break 0 0;
        print_clauses clauses;
        pp_close_box ();
        pp_string ")"
    | AE_let (v, e, b) ->
        pp_string "let ";
        pp_string (string_of_var v.v);
        pp_string " = ";
        print_aexp e;
        pp_string " in ";
        print_aexp b
    | AE_letpat (v, (av, occ), e) ->
        pp_string "letpat ";
        pp_string (string_of_var v.v);
        pp_string " = ";
        print_av av;
        pp_string (string_of_occurrence occ);
        pp_string " in ";
        print_aexp e

let print_const c =
  pp_open_vbox 0;
  pp_open_box 0;
  pp_string "const ";
  pp_string (string_of_var c.aconst_ident);
  pp_string " = ";
  print_aexp c.aconst_val;
  pp_close_box ();
  pp_newline ();
  pp_close_box ();
  pp_newline ()

let print_fun f =
  pp_open_vbox 0;
  pp_open_box 0;
  pp_string "fun ";
  pp_string (string_of_var f.afun_ident);
  pp_string "(";
  AstPrinter.print_list ", "
    (fun s -> pp_string (string_of_var s))
    f.afun_params;
  pp_string ") = {";
  pp_close_box ();
  pp_cut ();
  pp_open_box 2;
  pp_break 2 0;
  print_aexp f.afun_body;
  pp_close_box ();
  pp_newline ();
  pp_string "}";
  pp_newline ()

let rec print_clause (p, s) =
  pp_string "| ";
  print_pat p;
  pp_string " -> ";
  pp_cut ();
  pp_open_vbox 2;
  pp_string " { ";
  print_stmt s;
  pp_string " }";
  pp_close_box ()

and print_clauses = function
  | [] -> ()
  | [c] -> print_clause c
  | c :: t ->
      print_clause c;
      pp_break 1 0;
      print_clauses t

and print_stmt s =
  match s.astmt with
    | AS_set_var (v, e) ->
        pp_string (string_of_var v.v);
        pp_string " := ";
        print_aexp e
    | AS_set_field (v, f, e) ->
        pp_string (string_of_var v.v);
        pp_string ".";
        pp_string (Location.value f);
        pp_string " := ";
        print_aexp e
    | AS_let (v, e, s) ->
        pp_string "let ";
        pp_string (string_of_var v.v);
        pp_string " = ";
        print_aexp e;
        pp_string " in ";
        pp_cut ();
        pp_open_vbox 2;
        pp_string " { ";
        print_stmt s;
        pp_string " }";
        pp_close_box ()
    | AS_case (v, clauses) ->
        pp_open_vbox 2;
        pp_string "(case ";
        pp_string (string_of_var v.v);
        pp_string " of ";
        pp_break 0 0;
        print_clauses clauses;
        pp_close_box ();
        pp_string ")"
    | AS_block ss ->
        AstPrinter.print_list "; " print_stmt ss
    | AS_letpat (v, (av, occ), b) ->
        pp_string "letpat ";
        pp_string (string_of_var v.v);
        pp_string " = ";
        print_av av;
        pp_string (string_of_occurrence occ);
        print_stmt b
