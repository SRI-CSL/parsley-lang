open Parsing
open Anf
open Format


let ppf = ref std_formatter

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
        pp_print_string !ppf s
    | AV_var v ->
        pp_print_string !ppf (string_of_var v)
    | AV_constr (c, avs) ->
        pp_print_string !ppf (AstPrinter.string_of_constructor c);
        if List.length avs > 0 then begin
            pp_print_string !ppf "(";
            AstPrinter.print_list ", " print_av avs;
            pp_print_string !ppf ")";
          end
    | AV_record fields ->
        pp_print_string !ppf "{";
        AstPrinter.print_list ", " (fun (f, v) ->
            pp_print_string !ppf (Location.value f);
            pp_print_string !ppf ": ";
            print_av v
          ) fields;
        pp_print_string !ppf "}"
    | AV_mod_member (m, i) ->
        pp_print_string !ppf
          (Printf.sprintf "%s.%s" (Location.value m) (Location.value i))

let print_pat p =
  match p.apat with
    | AP_wildcard ->
        pp_print_string !ppf "_"
    | AP_literal l ->
        pp_print_string !ppf (AstPrinter.string_of_literal l)
    | AP_variant c ->
        pp_print_string !ppf (AstPrinter.string_of_constructor c)

let rec print_clause (p, e) =
  pp_print_string !ppf "| ";
  print_pat p;
  pp_print_string !ppf " -> ";
  print_aexp e

and print_clauses = function
  | [] -> ()
  | [c] -> print_clause c
  | c :: t ->
      print_clause c;
      pp_print_break !ppf 1 0;
      print_clauses t

and print_aexp e =
  match e.aexp with
    | AE_val v ->
        print_av v
    | AE_apply (f, vs) ->
        pp_print_string !ppf "(";
        print_av f;
        pp_print_string !ppf " ";
        AstPrinter.print_list " " print_av vs;
        pp_print_string !ppf ")"
    | AE_unop (op, v) ->
        pp_print_string !ppf (AstPrinter.str_of_unop op);
        pp_print_string !ppf "(";
        print_av v;
        pp_print_string !ppf ")"
    | AE_binop (Index, l, r) ->
        print_av l;
        pp_print_string !ppf "[";
        print_av r;
        pp_print_string !ppf "]"
    | AE_binop (b, l, r) ->
        pp_print_string !ppf "(";
        print_av l;
        let op = Printf.sprintf " %s " (AstPrinter.str_of_binop b) in
        pp_print_string !ppf op;
        print_av r;
        pp_print_string !ppf ")"
    | AE_recop (r, rop, v) ->
        let r = Printf.sprintf "%s->%s"
                  (Location.value r) (Location.value rop) in
        pp_print_string !ppf r;
        pp_print_string !ppf "(";
        print_av v;
        pp_print_string !ppf ")"
    | AE_bitrange (v, n, m) ->
        print_av v;
        pp_print_string !ppf "[[";
        pp_print_string !ppf (string_of_int n);
        pp_print_string !ppf ":";
        pp_print_string !ppf (string_of_int m);
        pp_print_string !ppf "]]"
    | AE_match (v, c) ->
        pp_print_string !ppf "(";
        print_av v;
        pp_print_string !ppf " ~~ ";
        pp_print_string !ppf (AstPrinter.string_of_constructor c);
        pp_print_string !ppf ")"
    | AE_field (v, f) ->
        print_av v;
        pp_print_string !ppf ".";
        pp_print_string !ppf (Location.value f)
    | AE_cast (v, t) ->
        pp_print_string !ppf "(";
        print_av v;
        pp_print_string !ppf " : ";
        AstPrinter.print_type_expr t;
        pp_print_string !ppf ")"
    | AE_case (v, clauses) ->
        pp_open_vbox !ppf 2;
        pp_print_string !ppf "(case ";
        pp_print_string !ppf (string_of_var v.v);
        pp_print_string !ppf " of ";
        pp_print_break !ppf 0 0;
        print_clauses clauses;
        pp_close_box !ppf ();
        pp_print_string !ppf ")"
    | AE_let (v, e, b) ->
        pp_print_string !ppf "let ";
        pp_print_string !ppf (string_of_var v.v);
        pp_print_string !ppf " = ";
        print_aexp e;
        pp_print_string !ppf " in ";
        print_aexp b
    | AE_letpat (v, (av, occ), e) ->
        pp_print_string !ppf "letpat ";
        pp_print_string !ppf (string_of_var v.v);
        pp_print_string !ppf " = ";
        print_av av;
        pp_print_string !ppf (string_of_occurrence occ);
        pp_print_string !ppf " in ";
        print_aexp e

let print_fun f =
  pp_open_vbox !ppf 0;
  pp_open_box !ppf 0;
  pp_print_string !ppf "fun ";
  pp_print_string !ppf (string_of_var f.afun_ident);
  pp_print_string !ppf "(";
  AstPrinter.print_list ", "
    (fun s -> pp_print_string !ppf (string_of_var s))
    f.afun_params;
  pp_print_string !ppf ") = {";
  pp_close_box !ppf ();
  pp_print_cut !ppf ();
  pp_open_box !ppf 2;
  pp_print_break !ppf 2 0;
  print_aexp f.afun_body;
  pp_close_box !ppf ();
  pp_print_newline !ppf ();
  pp_print_string !ppf "}";
  pp_print_newline !ppf ()

let rec print_clause (p, s) =
  pp_print_string !ppf "| ";
  print_pat p;
  pp_print_string !ppf " -> ";
  pp_print_cut !ppf ();
  pp_open_vbox !ppf 2;
  pp_print_string !ppf " { ";
  print_stmt s;
  pp_print_string !ppf " }";
  pp_close_box !ppf ()

and print_clauses = function
  | [] -> ()
  | [c] -> print_clause c
  | c :: t ->
      print_clause c;
      pp_print_break !ppf 1 0;
      print_clauses t

and print_stmt s =
  match s.astmt with
    | AS_set_var (v, e) ->
        pp_print_string !ppf (string_of_var v.v);
        pp_print_string !ppf " := ";
        print_aexp e
    | AS_set_field (v, f, e) ->
        pp_print_string !ppf (string_of_var v.v);
        pp_print_string !ppf ".";
        pp_print_string !ppf (Location.value f);
        pp_print_string !ppf " := ";
        print_aexp e
    | AS_let (v, e, s) ->
        pp_print_string !ppf "let ";
        pp_print_string !ppf (string_of_var v.v);
        pp_print_string !ppf " = ";
        print_aexp e;
        pp_print_string !ppf " in ";
        pp_print_cut !ppf ();
        pp_open_vbox !ppf 2;
        pp_print_string !ppf " { ";
        print_stmt s;
        pp_print_string !ppf " }";
        pp_close_box !ppf ()
    | AS_case (v, clauses) ->
        pp_open_vbox !ppf 2;
        pp_print_string !ppf "(case ";
        pp_print_string !ppf (string_of_var v.v);
        pp_print_string !ppf " of ";
        pp_print_break !ppf 0 0;
        print_clauses clauses;
        pp_close_box !ppf ();
        pp_print_string !ppf ")"
    | AS_block ss ->
        AstPrinter.print_list "; " print_stmt ss
    | AS_letpat (v, (av, occ), b) ->
        pp_print_string !ppf "letpat ";
        pp_print_string !ppf (string_of_var v.v);
        pp_print_string !ppf " = ";
        print_av av;
        pp_print_string !ppf (string_of_occurrence occ);
        print_stmt b
