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
  : Cfg.nt_entry * state * Cfg.closed =
  let venv = VEnv.empty in
  let fenv = FEnv.empty in
  let s = {st_spec_toc     = Cfg.(spec.ir_gtoc);
           st_spec_ir      = Cfg.(spec.ir_blocks);
           st_ir_tenv      = Cfg.(spec.ir_tenv);
           st_ir_venv      = Cfg.(spec.ir_venv);
           st_mode         = Mode_normal;
           st_venv         = venv;
           st_fenv         = fenv;
           st_view_stk     = [];
           st_cur_view     = view} in
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
  (* Get the entry block *)
  let loc = Location.loc ent.nt_name in
  let b   = get_block loc s (Cfg.L_static ent.nt_entry) in
  ent, s, b

let run_once ((ent: Cfg.nt_entry), (s: state), (b: Cfg.closed))
    : value option =
  let loc = Location.loc ent.nt_name in
  let code, s, l = Interpret_cfg.do_closed_block s b in
  match code with
    | C_success ->
        (* We should have terminated at the specified success
           continuation. *)
        assert (l = ent.nt_succcont);
        (* According to the calling convention, `ent.retvar`
           should hold the matched value in the value
           environment of `s'`. *)
        let vl = VEnv.lookup s.st_venv ent.nt_retvar.v loc in
        Some vl
    | C_failure ->
        (* We should have terminated at the specified failure
           continuation. *)
        assert (l = ent.nt_failcont);
        None

let run_loop ((ent: Cfg.nt_entry), (s: state), (b: Cfg.closed))
    : value list =
  let loc = Location.loc ent.nt_name in
  let rec loop acc s_init =
    let code, s, l = Interpret_cfg.do_closed_block s_init b in
    match code with
      | C_success ->
          (* We should have terminated at the specified success
             continuation. *)
          assert (l = ent.nt_succcont);
          (* According to the calling convention, `ent.retvar`
             should hold the matched value in the value
             environment of `s'`. *)
          let vl = VEnv.lookup s.st_venv ent.nt_retvar.v loc in
          (* Restore clean state but with updated view *)
          let s = {s_init with st_cur_view = s.st_cur_view} in
          loop (vl :: acc) s
    | C_failure ->
        (* We should have terminated at the specified failure
           continuation. *)
        assert (l = ent.nt_failcont);
        List.rev acc in
  loop [] s

let once_on_file spec entry f =
  run_once (init spec entry (Viewlib.from_file f))

let loop_on_file spec entry f =
  run_loop (init spec entry (Viewlib.from_file f))

let once_on_test_string test spec entry s =
  run_once (init spec entry (Viewlib.from_string test s))
