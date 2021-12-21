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

open Ir
open Values
open State
open Runtime_exceptions
open Interpret_anf
open Interpret_bitops

let interpret_gnode (s: state) (n: Cfg.gnode) : state =
  let loc = n.node_loc in
  match n.node with
    | N_assign (vr, fresh, ae) ->
        let vl = val_of_aexp s ae in
        let st_venv = VEnv.assign s.st_venv vr fresh vl in
        {s with st_venv}
    | N_assign_fun (fv, pvs, bd) ->
        let st_fenv = FEnv.assign s.st_fenv fv pvs bd in
        {s with st_fenv}
    | N_action sts ->
        List.fold_left eval_stmt s sts
    | N_bits w ->
        match_bits loc (Printf.sprintf "bits<%d>" w) s w
    | N_align w ->
        align_bits loc (Printf.sprintf "align<%d>" w) s w
    | N_pad w ->
        align_bits loc (Printf.sprintf "pad<%d>" w) s w
    | N_mark_bit_cursor ->
        mark_bit_cursor loc s
    | N_collect_bits (v, fresh, pred) ->
        let bits, s = collect_bits loc s in
        if   match_bits_bound bits pred
        then let bits = List.map (fun b -> V_bool b) bits in
             let env = VEnv.assign s.st_venv v fresh (V_list bits) in
             {s with st_venv = env}
        else let m = Ir_printer.string_of_mbb pred in
             let err = Internal_errors.Bitsbound_check (loc, m) in
             internal_error err
    | N_push_view ->
        let st_view_stk = s.st_cur_view :: s.st_view_stk in
        {s with st_view_stk}
    | N_pop_view
         when s.st_view_stk = [] ->
        let err = Internal_errors.View_stack_underflow loc in
        internal_error err
    | N_pop_view ->
        let vu, stk = List.hd s.st_view_stk, List.tl s.st_view_stk in
        {s with st_cur_view = vu;
                st_view_stk = stk}
    | N_set_view v ->
        let vl = VEnv.lookup s.st_venv v.v v.v_loc in
        Viewlib.set_view loc s vl
    | N_set_pos v ->
        let ps = VEnv.lookup s.st_venv v.v v.v_loc in
        Viewlib.set_pos loc s ps
