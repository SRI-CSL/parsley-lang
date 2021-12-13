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
open Flow
open Cfg
open Format

let pp_string    = pp_print_string !AstPrinter.ppf
let pp_open_box  = pp_open_box !AstPrinter.ppf
let pp_open_vbox = pp_open_vbox !AstPrinter.ppf
let pp_open_hbox = pp_open_hbox !AstPrinter.ppf
let pp_close_box = pp_close_box !AstPrinter.ppf
let pp_break     = pp_print_break !AstPrinter.ppf
let pp_flush     = pp_print_flush !AstPrinter.ppf
let pp_newline   = pp_print_newline !AstPrinter.ppf
let pp_cut       = pp_print_cut !AstPrinter.ppf
let pp_space     = pp_print_space !AstPrinter.ppf

let string_of_mbb = function
  | MB_exact i -> Printf.sprintf "ex %d" i
  | MB_below i -> Printf.sprintf "bl %d" i

let string_of_fresh f =
  if f then "/f" else ""

let string_of_return (r: return) =
  match r with
    | None ->
        "noret"
    | Some (v, f) ->
        Printf.sprintf "ret(%s%s)"
          (Anf_printer.string_of_var v.v)
          (string_of_fresh f)

(* assumed to be called from within a hbox *)
let print_gnode g =
  match g.node with
    | N_assign (v, f, ae) ->
        pp_string (Printf.sprintf "%s%s := "
                     (Anf_printer.string_of_var v.v)
                     (string_of_fresh f));
        Anf_printer.print_aexp ae
    | N_assign_fun (v, vs, bd) ->
        let args = List.map (fun v ->
                       Anf_printer.string_of_var Anf.(v.v)
                     ) vs in
        pp_string (Printf.sprintf "%s(%s) = "
                     (Anf_printer.string_of_var v.v)
                     (String.concat "," args)
          );
        Anf_printer.print_aexp bd
    | N_action ss ->
        pp_open_vbox 0;
        pp_string "{ ";
        List.iter (fun s ->
            Anf_printer.print_stmt s;
            pp_string ";";
            pp_space ()
          ) ss;
        pp_string " }";
        pp_close_box ()
    | N_bits i ->
        pp_string (Printf.sprintf "bits %d" i)
    | N_align i ->
        pp_string (Printf.sprintf "align %d" i)
    | N_pad (i, bv) ->
        let fb b = if b then "1" else "0" in
        let sbv = String.concat "" (List.map fb bv) in
        pp_string (Printf.sprintf "pad %d%s"
                     i
                     (if List.length bv = 0
                      then ""
                      else (" 0b" ^ sbv)))
    | N_mark_bit_cursor ->
        pp_string "bit_mark"
    | N_collect_bits (v, f, mbb) ->
        pp_string (Printf.sprintf "collect %s%s, %s"
                     (Anf_printer.string_of_var v.v)
                     (string_of_fresh f)
                     (string_of_mbb mbb))
    | N_push_view ->
        pp_string "push_view"
    | N_pop_view ->
        pp_string "pop_view"
    | N_set_view v ->
        pp_string (Printf.sprintf "set_view %s"
                     (Anf_printer.string_of_var v.v))
    | N_set_pos v ->
        pp_string (Printf.sprintf "set_pos %s"
                     (Anf_printer.string_of_var v.v))

(* assumed to be called from within a hbox *)
let print_node (type e x v) (n: (e, x, v) Node.node) =
  let open Node in
  match n with
    | N_label l ->
        pp_string (Printf.sprintf "L: %s" (Label.to_string l))
    | N_gnode g ->
        print_gnode g
    | N_push_failcont l ->
        pp_string (Printf.sprintf "push_fail %s" (Label.to_string l))
    | N_pop_failcont l ->
        pp_string (Printf.sprintf "pop_fail %s" (Label.to_string l))
    | N_jump l ->
        pp_string (Printf.sprintf "jmp %s" (Label.to_string l))
    | N_constraint (v, s, f) ->
        pp_string (Printf.sprintf "constr %s, %s, %s"
                     (Anf_printer.string_of_var v.v)
                     (Label.to_string s)
                     (Label.to_string f))
    | N_cond_branch (v, s, f) ->
        pp_string (Printf.sprintf "cbranch %s, %s, %s"
                     (Anf_printer.string_of_var v.v)
                     (Label.to_string s)
                     (Label.to_string f))
    | N_call_nonterm (nt, args, ret, s, f) ->
        let sargs = String.concat ","
                     (List.map (fun (a, (v: Anf.var)) ->
                          Printf.sprintf "%s<-%s"
                            (Location.value a)
                            (Anf_printer.string_of_var v.v)
                        ) args) in
        pp_string (Printf.sprintf "call %s[%s], %s, %s, %s"
                     (Location.value nt)
                     sargs
                     (string_of_return ret)
                     (Label.to_string s)
                     (Label.to_string f))
    | N_exec_dfa (_, v, s, f) ->
        pp_string (Printf.sprintf "dfa %s, %s, %s"
                     (Anf_printer.string_of_var v.v)
                     (Label.to_string s)
                     (Label.to_string f))

let print_opened (b: opened) =
  let h, ns = match b with
      | B.BlockCO (h, b') -> h, B.to_list b'
      | _ -> assert false in
  pp_open_hbox ();
  pp_string "[ ";
  print_node h;
  List.iter (fun n ->
      pp_string "; "; print_node n
    ) ns;
  pp_string " ]";
  pp_close_box ()

let print_closed (b: closed) =
  let h, ns, t = match b with
      | B.BlockCC (h, b', t) -> h, B.to_list b', t
      | _ -> assert false in
  pp_open_hbox ();
  pp_string "[ ";
  print_node h; pp_string "; ";
  List.iter (fun n ->
      print_node n; pp_string "; "
    ) ns;
  print_node t;
  pp_string " ]";
  pp_close_box ()

let string_of_nt_entry e =
  Printf.sprintf "{nt: %s, entry: %s, succ: %s, fail: %s}"
    (Location.value e.nt_name)
    (Label.to_string e.nt_entry)
    (Label.to_string e.nt_succcont)
    (Label.to_string e.nt_failcont)

let print_gtoc toc =
  pp_string "GTOC:"; pp_newline ();
  pp_open_hbox ();
  Seq.iter (fun (_, e) ->
      pp_string (string_of_nt_entry e);
      pp_newline ()
    ) (FormatGToC.to_seq toc);
  pp_close_box ()

let print_ir_blocks blocks =
  pp_string "Blocks:"; pp_newline ();
  Seq.iter (fun (l, b) ->
      pp_open_vbox 2;
      pp_string (Printf.sprintf "%s:" (Label.to_string l));
      pp_newline ();
      print_closed b;
      pp_newline ();
      pp_close_box ()
    ) (FormatIR.to_seq blocks)

let print_statics blocks =
  pp_string "Statics:"; pp_newline ();
  print_opened blocks;
  pp_newline ()

let print_spec ir =
  pp_open_vbox 0;
  print_gtoc ir.ir_gtoc;
  pp_newline ();
  print_ir_blocks ir.ir_blocks;
  pp_newline ();
  print_statics ir.ir_statics;
  pp_newline ();
  pp_string (Printf.sprintf "InitFailCont: %s"
               (Label.to_string ir.ir_init_failcont));
  pp_newline ();
  pp_close_box ()
