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
open Scf

let pp_string    = AstPrinter.pp_string
let pp_open_box  = AstPrinter.pp_open_box
let pp_open_vbox = AstPrinter.pp_open_vbox
let pp_open_hbox = AstPrinter.pp_open_hbox
let pp_close_box = AstPrinter.pp_close_box
let pp_break     = AstPrinter.pp_break
let pp_cut       = AstPrinter.pp_cut
let pp_newline   = AstPrinter.pp_newline
let pp_space     = AstPrinter.pp_space
let pp_flush     = AstPrinter.pp_flush

(* Control flow graph *)

let string_of_mbb = function
  | MB_exact i -> Printf.sprintf "ex %d" i
  | MB_below i -> Printf.sprintf "bl %d" i

let string_of_handle = function
  | H_success -> "success"
  | H_failure -> "failure"

let str_of_linst (li: linear_instr) : string =
  match li.li with
    | L_assign (v, _) ->
        Printf.sprintf "[%s := <.>]"
          (Anf_printer.string_of_var v)
    | L_assign_fun (v, vs, _, _) ->
        let args = List.map (fun v ->
                       Anf_printer.string_of_var v
                     ) vs in
        Printf.sprintf "[%s(%s) = <.>]"
          (Anf_printer.string_of_var v)
          (String.concat "," args)
    | L_assign_mod_var (m, v, _) ->
        Printf.sprintf "[%s.%s := <.>]"
          (Location.value m) (Location.value v)
    | L_assign_mod_fun (m, v, vs, _, _) ->
        let args = List.map (fun v ->
                       Anf_printer.string_of_var v
                     ) vs in
        Printf.sprintf "[%s.%s(%s) = <.>]"
          (Location.value m)
          (Location.value v)
          (String.concat "," args)
    | L_action ss ->
        Printf.sprintf "{%d stmts}"
          (List.length ss)
    | L_enter_bitmode ->
        "enter_bitmode"
    | L_exit_bitmode ->
        "exit_bitmode"
    | L_fail_bitmode ->
        "fail_bitmode"
    | L_mark_bit_cursor ->
        "set_bit_mark"
    | L_collect_bits (v, mbb, obf) ->
        let bf = match obf with
            | None    -> ""
            | Some bf -> Printf.sprintf "<%s>" bf.bf_name in
        Printf.sprintf "collect_bits%s %s, %s"
          bf (Anf_printer.string_of_var v) (string_of_mbb mbb)
    | L_push_view ->
        "push_view"
    | L_pop_view ->
        "pop_view"
    | L_drop_view ->
        "drop_view"
    | L_set_view v ->
        Printf.sprintf "set_view %s"
          (Anf_printer.string_of_var v)
    | L_set_pos v ->
        Printf.sprintf "set_pos %s"
          (Anf_printer.string_of_var v)
    | L_continue_choice ->
        "continue_choice"
    | L_finish_choice ->
        "finish_choice"
    | L_fail_choice ->
        "fail_choice"

let sprint_padding bv =
  let fb b = if b then "1" else "0" in
  let sbv = String.concat "" (List.map fb bv) in
  if   List.length bv = 0
  then ""
  else ", padding<0b" ^ sbv ^ ">"

let sprint_scan_dir = function
  | Ast.Scan_forward  -> "fw"
  | Ast.Scan_backward -> "bw"

let rec str_of_binst (bi: bivalent_instr) =
  match bi.bi with
    | B_linear l ->
        str_of_linst l
    | B_control c ->
        str_of_cinst c
    | B_fail ->
        "fail"
    | B_break ->
        "break"
    | B_bits i ->
        Printf.sprintf "bits %d" i
    | B_align i ->
        Printf.sprintf "align %d" i
    | B_pad i ->
        Printf.sprintf "pad %d" i
    | B_collect_checked_bits (v, (mbb, bv)) ->
        Printf.sprintf "collect_checked_bits %s, %s%s"
          (Anf_printer.string_of_var v)
          (string_of_mbb mbb)
          (sprint_padding bv)
    | B_check_bits (mbb, bv) ->
        Printf.sprintf "check_bits %s%s"
          (string_of_mbb mbb)
          (sprint_padding bv)
    | B_constraint v ->
        Printf.sprintf "constraint %s"
          (Anf_printer.string_of_var v)
    | B_exec_dfa (_, v) ->
        Printf.sprintf "dfa %s"
          (Anf_printer.string_of_var v)
    | B_scan ((t, d), v) ->
        Printf.sprintf "scan-%s \"%s\", %s"
          (sprint_scan_dir d)
          (Location.value t)
          (Anf_printer.string_of_var v)
    | B_call_nonterm (m, nt, args, ret) ->
        let sargs = String.concat ","
                      (List.map (fun (a, (v: Anf.var)) ->
                           Printf.sprintf "%s<-%s"
                             (Location.value a)
                             (Anf_printer.string_of_var v)
                         ) args) in
        Printf.sprintf "call %s[%s], %s"
          (Anf_common.mod_prefix m (Location.value nt))
          sargs
          (Anf_printer.string_of_var ret)
    | B_require_remaining (v, e) ->
        Printf.sprintf "require_remaining %s, %s"
          (Anf_printer.string_of_var v)
          (Anf_printer.string_of_var e)

and str_of_cinst (ci: ctrl_instr) =
  match ci.ci with
    | C_do (db, (hf, h)) ->
        Printf.sprintf "do [ %s ] handle %s [ %s ]"
          (str_of_block db)
          (string_of_handle hf)
          (str_of_handler h)
    | C_loop (f, lb) ->
        Printf.sprintf "%sloop [ %s ]"
          (if f then "i" else "b")
          (str_of_block lb)
    | C_if (v, tb, eb) ->
        Printf.sprintf "if %s [ %s ] [ %s ]"
          (Anf_printer.string_of_var v)
          (str_of_block tb)
          (str_of_block eb)
    | C_start_choices (f, _vs, cb) ->
        (* TODO: FIXME: print `vs` *)
        Printf.sprintf "start_choices(%s, VARS) [ %s ]"
          (Anf.str_of_frame_id f)
          (str_of_block cb)

and str_of_block : sealed_block -> string = function
  | `Sealed b ->
      String.concat " " (List.map str_of_binst b)

and str_of_handler : sealed_handler -> string = function
  | `Sealed h ->
      String.concat " " (List.map str_of_linst h)

let print_linst (li: linear_instr) =
  match li.li with
    | L_assign (v, ae) ->
        pp_string (Printf.sprintf "%s := "
                     (Anf_printer.string_of_var v));
        Anf_printer.print_aexp ae
    | L_assign_fun (v, vs, bd, _) ->
        let args = List.map (fun v ->
                       Anf_printer.string_of_var v
                     ) vs in
        pp_string (Printf.sprintf "%s(%s) = "
                     (Anf_printer.string_of_var v)
                     (String.concat "," args)
          );
        Anf_printer.print_aexp bd
    | L_assign_mod_var (m, v, ae) ->
        pp_string (Printf.sprintf "%s.%s := "
                     (Location.value m) (Location.value v));
        Anf_printer.print_aexp ae
    | L_assign_mod_fun (m, v, vs, bd, _) ->
        let args = List.map (fun v ->
                       Anf_printer.string_of_var v
                     ) vs in
        pp_string (Printf.sprintf "%s.%s(%s) = "
                     (Location.value m)
                     (Location.value v)
                     (String.concat "," args)
          );
        Anf_printer.print_aexp bd
    | L_action ss ->
        pp_open_vbox 0;
        pp_string "{ ";
        List.iter (fun s ->
            Anf_printer.print_stmt s;
            pp_string ";";
            pp_space ()
          ) ss;
        pp_string " }";
        pp_close_box ()
    | L_enter_bitmode ->
        pp_string "enter_bitmode"
    | L_exit_bitmode ->
        pp_string "exit_bitmode"
    | L_fail_bitmode ->
        pp_string "fail_bitmode"
    | L_mark_bit_cursor ->
        pp_string "set_bit_mark"
    | L_collect_bits (v, mbb, obf) ->
        let bf = match obf with
            | None    -> ""
            | Some bf -> Printf.sprintf "<%s>" bf.bf_name in
        pp_string (Printf.sprintf "collect_bits%s %s, %s"
                     bf (Anf_printer.string_of_var v)
                     (string_of_mbb mbb))
    | L_push_view ->
        pp_string "push_view"
    | L_pop_view ->
        pp_string "pop_view"
    | L_drop_view ->
        pp_string "drop_view"
    | L_set_view v ->
        pp_string (Printf.sprintf "set_view %s"
                     (Anf_printer.string_of_var v))
    | L_set_pos v ->
        pp_string (Printf.sprintf "set_pos %s"
                     (Anf_printer.string_of_var v))

    | L_continue_choice ->
        pp_string "continue_choice"
    | L_finish_choice ->
        pp_string "finish_choice"
    | L_fail_choice ->
        pp_string "fail_choice"

let rec print_binst (bi: bivalent_instr) =
  match bi.bi with
    | B_linear l ->
        print_linst l
    | B_control c ->
        print_cinst c

    | B_fail ->
        pp_string "fail"
    | B_break ->
        pp_string "break"

    | B_bits i ->
        pp_string (Printf.sprintf "bits %d" i)
    | B_align i ->
        pp_string (Printf.sprintf "align %d" i)
    | B_pad i ->
        pp_string (Printf.sprintf "pad %d" i)
    | B_collect_checked_bits (v, (mbb, bv)) ->
        pp_string (Printf.sprintf "collect_checked_bits %s, %s%s"
                     (Anf_printer.string_of_var v)
                     (string_of_mbb mbb)
                     (sprint_padding bv))
    | B_check_bits (mbb, bv) ->
        pp_string (Printf.sprintf "check_bits %s%s"
                     (string_of_mbb mbb)
                     (sprint_padding bv))
    | B_constraint v ->
        pp_string (Printf.sprintf "constraint %s"
                     (Anf_printer.string_of_var v))
    | B_exec_dfa (_, v) ->
        pp_string (Printf.sprintf "dfa %s"
                     (Anf_printer.string_of_var v))
    | B_scan ((t, d), v) ->
        pp_string (Printf.sprintf "scan-%s \"%s\", %s"
                     (sprint_scan_dir d)
                     (Location.value t)
                     (Anf_printer.string_of_var v))
    | B_call_nonterm (m, nt, args, ret) ->
        let sargs = String.concat ","
                     (List.map (fun (a, (v: Anf.var)) ->
                          Printf.sprintf "%s<-%s"
                            (Location.value a)
                            (Anf_printer.string_of_var v)
                        ) args) in
        pp_string (Printf.sprintf "call %s[%s], %s"
                     (Anf_common.mod_prefix m (Location.value nt))
                     sargs
                     (Anf_printer.string_of_var ret))
    | B_require_remaining (v, e) ->
        pp_string (Printf.sprintf "require_remaining %s, %s"
                     (Anf_printer.string_of_var v)
                     (Anf_printer.string_of_var e))

and print_cinst (ci: ctrl_instr) =
  match ci.ci with
    | C_do (db, (hf, h)) ->
        pp_open_vbox 2;
        pp_string "do [ ";
        print_block db;
        pp_close_box ();
        pp_string " ]";
        pp_open_vbox 2;
        pp_string (Printf.sprintf " handle %s ["
                     (string_of_handle hf));
        print_handler h;
        pp_close_box ();
        pp_string " ]"
    | C_loop (f, lb) ->
        pp_open_vbox 2;
        pp_string (Printf.sprintf "%sloop [ "
                     (if f then "i" else "b"));
        print_block lb;
        pp_close_box ();
        pp_string " ]"
    | C_if (v, tb, eb) ->
        pp_open_vbox 2;
        pp_string (Printf.sprintf "if %s ["
                     (Anf_printer.string_of_var v));
        print_block tb;
        pp_string "] else [";
        print_block eb;
        pp_close_box ();
        pp_string "]"
    | C_start_choices (f, _vs, cb) ->
        (* TODO: FIXME: print `vs` *)
        pp_open_vbox 2;
        pp_string (Printf.sprintf "start_choices(%s, VARS) ["
                     (Anf.str_of_frame_id f));
        print_block cb;
        pp_close_box ();
        pp_string "]"

and print_block : sealed_block -> unit = function
  | `Sealed b ->
      pp_open_vbox 2;
      List.iter (fun i ->
          print_binst i;
          pp_string "; ";
          pp_cut ()
        ) b;
      pp_close_box ()

and print_handler : sealed_handler -> unit = function
  | `Sealed h ->
      pp_open_vbox 2;
      List.iter (fun i ->
          print_linst i;
          pp_string "; ";
          pp_cut ()
        ) h;
      pp_close_box ()

let string_of_nt_entry (e: nt_entry) : string =
  Printf.sprintf "{nt: %s, var: %s}"
    (Location.value  e.nt_name)
    (Anf_printer.string_of_var e.nt_retvar)

let print_globals (g: nt_entry ValueMap.t) =
  pp_string "Globals:"; pp_newline ();
  pp_open_hbox ();
  Seq.iter (fun (_, e) ->
      pp_string (string_of_nt_entry e);
      pp_newline ();
      print_block e.nt_code;
      pp_newline ();
    ) (ValueMap.to_seq g);
  pp_close_box ()

let print_statics b =
  pp_string "Statics:"; pp_newline ();
  print_block b;
  pp_newline ()

let print_spec scf =
  pp_newline ();
  pp_open_vbox 0;
  print_globals scf.scf_globals;
  pp_newline ();
  print_statics scf.scf_statics;
  pp_newline ();
  pp_close_box ();
  pp_flush ()
