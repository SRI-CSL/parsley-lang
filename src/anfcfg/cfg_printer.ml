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

let pp_string    = AstPrinter.pp_string
let pp_open_box  = AstPrinter.pp_open_box
let pp_open_vbox = AstPrinter.pp_open_vbox
let pp_open_hbox = AstPrinter.pp_open_hbox
let pp_close_box = AstPrinter.pp_close_box
let pp_break     = AstPrinter.pp_break
let pp_newline   = AstPrinter.pp_newline
let pp_space     = AstPrinter.pp_space
let pp_flush     = AstPrinter.pp_flush

(* Control flow graph *)

let string_of_mbb = function
  | MB_exact i -> Printf.sprintf "ex %d" i
  | MB_below i -> Printf.sprintf "bl %d" i

let string_of_return (r: return) =
  match r with
    | None ->
        "noret"
    | Some v ->
        Printf.sprintf "ret(%s)"
          (Anf_printer.string_of_var v.v)

(* assumed to be called from within a hbox *)
let print_gnode g =
  match g.node with
    | N_assign (v, ae) ->
        pp_string (Printf.sprintf "%s := "
                     (Anf_printer.string_of_var v.v));
        Anf_printer.print_aexp ae
    | N_assign_fun (v, vs, bd, _) ->
        let args = List.map (fun v ->
                       Anf_printer.string_of_var Anf.(v.v)
                     ) vs in
        pp_string (Printf.sprintf "%s(%s) = "
                     (Anf_printer.string_of_var v.v)
                     (String.concat "," args)
          );
        Anf_printer.print_aexp bd
    | N_assign_mod_var (m, v, ae) ->
        pp_string (Printf.sprintf "%s.%s := "
                     (Location.value m) (Location.value v));
        Anf_printer.print_aexp ae
    | N_assign_mod_fun (m, v, vs, bd, _) ->
        let args = List.map (fun v ->
                       Anf_printer.string_of_var Anf.(v.v)
                     ) vs in
        pp_string (Printf.sprintf "%s.%s(%s) = "
                     (Location.value m)
                     (Location.value v)
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
    | N_enter_bitmode ->
        pp_string "enter_bitmode"
    | N_exit_bitmode ->
        pp_string "exit_bitmode"
    | N_fail_bitmode ->
        pp_string "fail_bitmode"
    | N_mark_bit_cursor ->
        pp_string "set_bit_mark"
    | N_collect_bits (v, mbb, obf) ->
        let bf = match obf with
            | None    -> ""
            | Some bf -> Printf.sprintf "<%s>" bf.bf_name in
        pp_string (Printf.sprintf "collect_bits%s %s, %s"
                     bf (Anf_printer.string_of_var v.v)
                     (string_of_mbb mbb))
    | N_push_view ->
        pp_string "push_view"
    | N_pop_view ->
        pp_string "pop_view"
    | N_drop_view ->
        pp_string "drop_view"
    | N_set_view v ->
        pp_string (Printf.sprintf "set_view %s"
                     (Anf_printer.string_of_var v.v))
    | N_set_pos v ->
        pp_string (Printf.sprintf "set_pos %s"
                     (Anf_printer.string_of_var v.v))

(* assumed to be called from within a hbox *)
let print_node (type e x v) (n: (e, x, v) Node.node) =
  let sprint_padding bv =
    let fb b = if b then "1" else "0" in
    let sbv = String.concat "" (List.map fb bv) in
    if   List.length bv = 0
    then ""
    else ", padding<0b" ^ sbv ^ ">" in
  let sprint_scan_dir = function
    | Ast.Scan_forward  -> "fw"
    | Ast.Scan_backward -> "bw" in
  let open Node in
  match n with
    | N_label (_, l, _) ->
        pp_string (Printf.sprintf "L: %s" (Label.to_string l))
    | N_gnode g ->
        print_gnode g
    | N_jump (_, l) ->
        pp_string (Printf.sprintf "jmp %s" (string_of_label l))
    | N_return (_, l) ->
        pp_string (Printf.sprintf "return %s" (string_of_label l))
    | N_bits (_, i, lsc, lf) ->
        pp_string (Printf.sprintf "bits %d, %s, %s"
                     i (string_of_label lsc) (string_of_label lf))
    | N_align (_, i, lsc, lf) ->
        pp_string (Printf.sprintf "align %d, %s, %s"
                     i (string_of_label lsc) (string_of_label lf))
    | N_pad (_, i, lsc, lf) ->
        pp_string (Printf.sprintf "pad %d, %s, %s"
                     i (string_of_label lsc) (string_of_label lf))
    | N_collect_checked_bits (_, v, (mbb, bv), lsc, lf) ->
        pp_string (Printf.sprintf "collect_checked_bits %s, %s%s, %s, %s"
                     (Anf_printer.string_of_var v.v)
                     (string_of_mbb mbb)
                     (sprint_padding bv)
                     (string_of_label lsc)
                     (string_of_label lf))
    | N_check_bits (_, (mbb, bv), lsc, lf) ->
        pp_string (Printf.sprintf "check_bits %s%s, %s, %s"
                     (string_of_mbb mbb)
                     (sprint_padding bv)
                     (string_of_label lsc)
                     (string_of_label lf))
    | N_constraint (_, v, s, f) ->
        pp_string (Printf.sprintf "constraint %s, %s, %s"
                     (Anf_printer.string_of_var v.v)
                     (string_of_label s)
                     (string_of_label f))
    | N_cond_branch (_, v, s, f) ->
        pp_string (Printf.sprintf "cbranch %s, %s, %s"
                     (Anf_printer.string_of_var v.v)
                     (string_of_label s)
                     (string_of_label f))
    | N_exec_dfa (_, v, s, f) ->
        pp_string (Printf.sprintf "dfa %s, %s, %s"
                     (Anf_printer.string_of_var v.v)
                     (string_of_label s)
                     (string_of_label f))
    | N_scan (_, (t, d), v, s, f) ->
        pp_string (Printf.sprintf "scan-%s \"%s\", %s, %s, %s"
                     (sprint_scan_dir d)
                     (Location.value t)
                     (Anf_printer.string_of_var v.v)
                     (string_of_label s)
                     (string_of_label f))
    | N_call_nonterm (m, nt, args, ret, s, f) ->
        let sargs = String.concat ","
                     (List.map (fun (a, (v: Anf.var)) ->
                          Printf.sprintf "%s<-%s"
                            (Location.value a)
                            (Anf_printer.string_of_var v.v)
                        ) args) in
        pp_string (Printf.sprintf "call %s[%s], %s, %s, %s"
                     (Anf.mod_prefix m (Location.value nt))
                     sargs
                     (string_of_return ret)
                     (string_of_label s)
                     (string_of_label f))
    | N_require_remaining (v, e, lr, ln) ->
        pp_string (Printf.sprintf "require_remaining %s, %s, %s, %s"
                     (Anf_printer.string_of_var v.v)
                     (Anf_printer.string_of_var e.v)
                     (string_of_label lr)
                     (string_of_label ln))

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
  Printf.sprintf "{nt: %s, entry: %s, succ: %s, fail: %s, var: %s}"
    (Location.value  e.nt_name)
    (Label.to_string e.nt_entry)
    (string_of_label e.nt_succcont)
    (string_of_label e.nt_failcont)
    (Anf_printer.string_of_var e.nt_retvar.v)

let print_gtoc toc =
  pp_string "GTOC:"; pp_newline ();
  pp_open_hbox ();
  Seq.iter (fun (_, e) ->
      pp_string (string_of_nt_entry e);
      pp_newline ()
    ) (ValueMap.to_seq toc);
  pp_close_box ()

let print_blocks blocks =
  pp_string "Blocks:"; pp_newline ();
  Seq.iter (fun (l, b) ->
      pp_open_vbox 2;
      pp_string (Printf.sprintf "%s:" (Label.to_string l));
      pp_newline ();
      print_closed b;
      pp_newline ();
      pp_close_box ()
    ) (LabelMap.to_seq blocks)

let print_statics blocks =
  pp_string "Statics:"; pp_newline ();
  print_opened blocks;
  pp_newline ()

let print_spec cfg =
  pp_newline ();
  pp_open_vbox 0;
  print_gtoc cfg.cfg_gtoc;
  pp_newline ();
  print_blocks cfg.cfg_blocks;
  pp_newline ();
  print_statics cfg.cfg_statics;
  pp_newline ();
  pp_string (Printf.sprintf "InitFailCont: %s"
               (string_of_label cfg.cfg_init_failcont));
  pp_newline ();
  pp_close_box ();
  pp_flush ()
