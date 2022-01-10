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

(* Interpret a Parsley spec on the data in a given file, given a
   top-level entry (user-defined) non-terminal. *)
let do_execute (spec: Cfg.spec_ir) (entry_nt: string) (view: view)
  : value option =
  let venv = VEnv.empty in
  let fenv = FEnv.empty in
  let failcont = Cfg.(spec.ir_init_failcont) in
  let s = {st_spec_toc     = Cfg.(spec.ir_gtoc);
           st_spec_ir      = Cfg.(spec.ir_blocks);
           st_ir_tenv      = Cfg.(spec.ir_tenv);
           st_ir_venv      = Cfg.(spec.ir_venv);
           st_mode         = Mode_normal;
           st_venv         = venv;
           st_fenv         = fenv;
           st_failcont_stk = [failcont];
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
  (* Adapt the code for N_call_nonterm, except there is now no
     continuation. *)
  let loc = Location.loc ent.nt_name in
  let b   = get_block loc s (Cfg.L_static ent.nt_entry) in
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

let execute_on_file spec entry_nt f =
  do_execute spec entry_nt (Viewlib.from_file f)

let execute_on_test_string test spec entry s =
  do_execute spec entry (Viewlib.from_string test s)
