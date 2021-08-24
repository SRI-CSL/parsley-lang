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
open Anf
open Cfg
open Anf_printer

let str_of_matched_bits_bound = function
  | MB_exact i -> Printf.sprintf "Exact(%d)" i
  | MB_below i -> Printf.sprintf "Below(%d)" i

let pr_gnode n =
  match n with
    | N_assign (v, fresh, ae) ->
        pp_string (Printf.sprintf "%s%s%s := "
                     (if fresh then "(" else "")
                     (string_of_var v.v)
                     (if fresh then ")" else ""));
        pp_open_box 0;
        print_aexp ae;
        pp_close_box ()
    | N_action ss ->
        AstPrinter.print_list "; " print_stmt ss
    | N_bits i ->
        pp_string (Printf.sprintf "bits %d" i)
    | N_align i ->
        pp_string (Printf.sprintf "align %d" i)
    | N_pad (i, _) ->
        pp_string (Printf.sprintf "pad %d _" i)
    | N_mark_bit_cursor ->
        pp_string "mark-bit-cursor"
    | N_collect_bits (v, fresh, b) ->
        pp_string (Printf.sprintf "%s%s%s := collect-bits %s"
                     (if fresh then "(" else "")
                     (string_of_var v.v)
                     (if fresh then ")" else "")
                     (str_of_matched_bits_bound b))
    | N_push_view ->
        pp_string "push-view"
    | N_pop_view ->
        pp_string "pop-view"
    | N_set_view v ->
        pp_string
          (Printf.sprintf "set-view %s" (string_of_var v.v))
    | N_set_pos v ->
        pp_string
          (Printf.sprintf "set-pos %s" (string_of_var v.v))

let pr_node (type e x) (n: (e, x, unit) Node.node) =
  pp_open_vbox 2;
  pp_string "[ ";
  (match n with
     | Node.N_label l ->
         pp_string (Printf.sprintf "label %s" (Label.to_string l))
     | Node.N_gnode nd ->
         pr_gnode nd.node
     | Node.N_push_failcont l ->
         pp_string (Printf.sprintf "push-failcont %s" (Label.to_string l))
     | Node.N_pop_failcont l ->
         pp_string (Printf.sprintf "pop-failcont %s" (Label.to_string l))
     | Node.N_jump l ->
         pp_string (Printf.sprintf "jump %s" (Label.to_string l))
     | Node.N_constraint (v, s, f) ->
         pp_string (Printf.sprintf "constraint %s -> %s // %s"
                      (string_of_var v.v)
                      (Label.to_string s)
                      (Label.to_string f))
     | Node.N_cond_branch (v, s, f) ->
         pp_string (Printf.sprintf "cond-branch %s -> %s | %s"
                      (string_of_var v.v)
                      (Label.to_string s)
                      (Label.to_string f))
     | Node.N_call_nonterm (nt, attrs, _ret, s, f) ->
         pp_string (Printf.sprintf "call %s (" (Location.value nt));
         AstPrinter.print_list ", " (fun (a, v) ->
             let s = Printf.sprintf "%s=%s" (Location.value a)
                       (string_of_var v.v) in
             pp_string s
           ) attrs;
         pp_string (Printf.sprintf ") -> %s // %s"
                      (Label.to_string s) (Label.to_string f))
  );
  pp_close_box ()
