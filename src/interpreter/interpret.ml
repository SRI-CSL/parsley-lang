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
open Ir
open State
open Values

(* Returns the entry block for the given non-terminal along with the
   interpreter state that is initialized by executing the static block. *)
let init (spec: Cfg.spec_ir) (entry_nt: string) (view: view)
  : state * Cfg.closed =
  let venv  = VEnv.empty in
  let fenv  = FEnv.empty in
  let mvenv = MVEnv.empty in
  let mfenv = MFEnv.empty in
  let s = {st_spec_toc     = Cfg.(spec.ir_gtoc);
           st_spec_ir      = Cfg.(spec.ir_blocks);
           st_ir_tenv      = Cfg.(spec.ir_tenv);
           st_ir_venv      = Cfg.(spec.ir_venv);
           st_mode         = Mode_normal;
           st_venv         = venv;
           st_fenv         = fenv;
           st_mvenv        = mvenv;
           st_mfenv        = mfenv;
           st_view_stk     = [];
           st_cur_view     = view;
           st_ctrl_stk     = []} in
  (* Initialize from the statics block. *)
  let s = Interpret_cfg.do_opened_block s Cfg.(spec.ir_statics) in
  (* Look up the entry non-terminal. *)
  let ent = match get_init_ntentry s entry_nt with
      | Some b -> b
      | None   -> (Printf.eprintf
                     "Unknown user-defined non-terminal `%s' specified.\n"
                     entry_nt;
                   exit 1) in
  (* In the interpreter, we cannot support entry non-terminals with
     inherited attributes, since their values cannot easily be
     specified on the command line. *)
  let niattrs = Cfg.StringMap.cardinal ent.nt_inh_attrs in
  if   niattrs > 0
  then (Printf.eprintf
          "The interpreter does not support an entry non-terminal with inherited attributes.\n";
        Printf.eprintf
          "The non-terminal `%s' has %d inherited attributes.\n"
          entry_nt niattrs;
        exit 1);
  (* Set up the top-level call frame (with no return
     continuations). *)
  let cf = {cf_nt          = ent.nt_name;
            cf_conts       = None;
            cf_nt_succcont = ent.nt_succcont;
            cf_nt_failcont = ent.nt_failcont;
            cf_nt_retvar   = ent.nt_retvar;
            cf_call_retvar = None;
            cf_call_state  = s} in
  let s = {s with st_ctrl_stk = [cf]} in
  (* Get the entry block *)
  let loc = Location.loc ent.nt_name in
  let b   = get_block loc s (Cfg.L_static ent.nt_entry) in
  s, b

(* returns the `vu_ofs` and `vu_end` of the view in the state. *)
type last_pos = int * int
let view_info (s: state) : last_pos =
  let v = s.st_cur_view in
  v.vu_ofs, v.vu_end

let run_once ((s: state), (b: Cfg.closed))
    : value option * last_pos =
  let r, s = Interpret_cfg.do_closed_block s b in
  match r with
    | Ok v     -> Some v, view_info s
    | Error s' -> None,   view_info s'

let run_loop ((s: state), (b: Cfg.closed))
    : value list * last_pos =
  let rec loop acc s_init =
    match Interpret_cfg.do_closed_block s_init b with
      | Ok vl, s ->
          loop (vl :: acc) {s_init with st_cur_view = s.st_cur_view}
      | Error s, _ ->
          List.rev acc, view_info s in
  loop [] s

let once_on_file spec entry f =
  run_once (init spec entry (Viewlib.from_file f))

let loop_on_file spec entry f =
  run_loop (init spec entry (Viewlib.from_file f))

let once_on_test_string test spec entry s =
  run_once (init spec entry (Viewlib.from_string test s))
