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
open Typing
open Anfcfg
open Interpreter_common
open Values
open Runtime_exceptions
open State

let init_runtime _ =
  (* Initialize standard dispatch table. *)
  Dispatch.initialize_dispatch Parsleylib.stdlib_mods

(* Each function declared to be external should have a corresponding
   loaded external implementation.

   For now, resolution is only done for the OCaml interpreter;
   i.e. for FFI decls specifying "ocaml" as a language.  The
   resolution uses the number of arguments in the signature, but does
   not check the types involved.  *)

let resolve_foreign (ffs: TypedAst.ffi_decl Cfg.ValueMap.t) =
  (* Create lookup table of externals. *)
  let etable = Dispatch.create_dtable () in
  Dispatch.update_dtable etable Externals.ext_mods;
  (* For each foreign function, look up the corresponding declared
     OCaml implementation.  If found, register it in the dispatch
     table linked to the name it will be invoked by. *)
  Cfg.ValueMap.iter (fun (m, fn) fd ->
      let loc = Ast.(fd.ffi_decl_loc) in
      let mn = (match m with
                  | Anf_common.M_name mn -> mn
                  | Anf_common.M_stdlib  -> assert false) in
      let nargs = List.length Ast.(fd.ffi_decl_params) in
      assert (fn = Ast.var_name Ast.(fd.ffi_decl_ident));
      (* Get the name of the external implementation, if any. *)
      let em, ef =
        match AstUtils.ocaml_binding Ast.(fd.ffi_decl_langs) with
          | None ->
              let err = No_foreign_impl_decl (mn, fn, nargs) in
              fault loc err
          | Some (m, f) ->
              m, f in
      (* Look up the implementing function in our externals table. *)
      let throw_not_found () =
        let err = No_foreign_impl_found (mn, fn, nargs) in
        fault loc err in
      match nargs with
        | 0 -> (match Dispatch.find_impl_arg0 etable em ef with
                  | None ->
                      throw_not_found ()
                  | Some impl ->
                      Dispatch.register_impl_arg0 mn fn impl)
        | 1 -> (match Dispatch.find_impl_arg1 etable em ef with
                  | None ->
                      throw_not_found ()
                  | Some impl ->
                      Dispatch.register_impl_arg1 mn fn impl)
        | 2 -> (match Dispatch.find_impl_arg2 etable em ef with
                  | None ->
                      throw_not_found ()
                  | Some impl ->
                      Dispatch.register_impl_arg2 mn fn impl)
        | 3 -> (match Dispatch.find_impl_arg3 etable em ef with
                  | None ->
                      throw_not_found ()
                  | Some impl ->
                      Dispatch.register_impl_arg3 mn fn impl)
        | _ -> throw_not_found ()
    ) ffs

(* Returns the entry block for the given non-terminal along with the
   interpreter state that is initialized by executing the static block. *)
let init load_externals (spec: Cfg.spec_cfg)
      (entry_nt: Anf_common.modul * string) (view: view)
    : state * Cfg.closed =
  (* Resolve externals in FFI. *)
  if   load_externals
  then resolve_foreign Cfg.(spec.cfg_foreigns);
  (* Initialize state. *)
  let venv  = VEnv.empty in
  let fenv  = FEnv.empty in
  let mvenv = MVEnv.empty in
  let mfenv = MFEnv.empty in
  let s = {st_spec_toc     = Cfg.(spec.cfg_gtoc);
           st_spec_cfg     = Cfg.(spec.cfg_blocks);
           st_cfg_tenv     = Cfg.(spec.cfg_tenv);
           st_cfg_venv     = Cfg.(spec.cfg_venv);
           st_mode         = Mode_normal;
           st_venv         = venv;
           st_fenv         = fenv;
           st_mvenv        = mvenv;
           st_mfenv        = mfenv;
           st_view_stk     = [];
           st_cur_view     = view;
           st_ctrl_stk     = []} in
  (* Initialize from the statics block. *)
  let s = Interpret_cfg.do_opened_block s Cfg.(spec.cfg_statics) in
  (* Look up the entry non-terminal. *)
  let ent = match get_init_ntentry s entry_nt with
      | Some b -> b
      | None   -> (Printf.eprintf
                     "Unknown user-defined non-terminal `%s' specified.\n"
                     (snd entry_nt);
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
          (snd entry_nt) niattrs;
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

(* Returns the parse call stack. *)
type parse_stk = Ast.ident list
let parse_info (s: state) : parse_stk =
  List.map (fun cf -> cf.cf_nt) s.st_ctrl_stk

(* Info for reporting state at the end of parse. *)
type error_info = last_pos * parse_stk
let error_info (s: state) : error_info =
  view_info s, parse_info s

(* The application-Parsley interface (API) is a crucial trust domain
   crossing that needs to be carefully delineated.  For now, the rough
   boundary is:  the functions above run on the Parsley side of the
   API, while the functions below run on the application side. *)

(* Top-level loop over parser.  This will run on the application-side
   of the API, and hence has access to and can invoke the
   pause-handler. *)
let loop_over_pauses (s: state) (b: Cfg.closed)
      (ph: App_viewlib.pause_handler) : value option * state =
  let do_refill refiller needed : (bytes, int) result =
    let rec loop needed bytes =
      match refiller needed with
        | Some bs ->
            let nbs = Bytes.length bs in
            let bytes = Bytes.cat bytes bs in
            if   nbs >= needed
            then Ok bytes
            else loop (needed - nbs) bytes
        | None ->
            (* TODO: should we really drop bytes read so far? *)
            Error needed in
    loop needed Bytes.empty in
  let handled_pause r ph : (unit, error) result =
    match r, ph with
      | Paused_require_refill _,
        {App_viewlib.ph_require_refill = None; _} ->
          Error Refill_no_handler
      | Paused_require_refill (vu, _), _
           when not (buf_is_refillable !(vu.vu_buf)) ->
          (* This really needs to be handled as an application
             configuration error. *)
          assert false
      | Paused_require_refill (vu, need),
        {App_viewlib.ph_require_refill = Some refiller; _} ->
          (match do_refill refiller need with
             | Error got ->
                 Error (Refill_failed (need, got))
             | Ok bytes ->
                 (* The invariant the refill handler must obey is that
                    it can only add data to the end of the buffer;
                    i.e. data already present in the buffer should be
                    left intact at their original offsets.  This
                    ensures that all existing views based on this
                    buffer remain valid after the refill. *)
                 let buf = buf_refill !(vu.vu_buf) bytes in
                 vu.vu_buf := buf;
                 Ok ()) in
  let rec loop s b =
    let r, s = Interpret_cfg.do_closed_block s b in
    match r with
      | Cfg_ok v              -> Some v, s
      | Cfg_error s'          -> None,   s'
      | Cfg_paused (lc, r, l) ->
          (match handled_pause r ph with
             | Ok _    -> let b = get_block lc s l in
                          loop s b
             | Error e -> fault lc e) in
  loop s b

(* Execute the CFG from the given starting block for a single result. *)
let run_once ((s: state), (b: Cfg.closed)) (ph: App_viewlib.pause_handler)
    : value option * error_info =
  let vo, s = loop_over_pauses s b ph in
  vo, error_info s

(* Execute the CFG from the given starting block for as many
   successful results as possible, restarting at the given block after
   a success, and stopping at the first failure. *)
let run_loop ((s: state), (b: Cfg.closed)) (ph: App_viewlib.pause_handler)
    : value list * error_info =
  let rec loop acc s_init =
    match loop_over_pauses s_init b ph with
      | Some v, s ->
          loop (v :: acc) {s_init with st_cur_view = s.st_cur_view}
      | None, s ->
          List.rev acc, error_info s in
  loop [] s

(* Top-level application-side entry points. *)

type input =
  | Inp_file of string
  | Inp_stdin of int
  | Inp_string of string * string

let open_input i =
  match i with
    | Inp_file f           -> App_viewlib.from_static_file f
    | Inp_stdin sz         -> App_viewlib.from_channel "stdin" Stdlib.stdin sz
    | Inp_string (test, s) -> App_viewlib.from_string test s

let once_on_file load_externals spec entry f =
  init_runtime load_externals;
  let v, pause_handler = open_input f in
  run_once (init load_externals spec entry v) pause_handler

let loop_on_file load_externals spec entry f =
  init_runtime load_externals;
  let v, pause_handler = open_input f in
  run_loop (init load_externals spec entry v) pause_handler

let once_on_test_string test spec entry s =
  let v, pause_handler = open_input (Inp_string (test, s)) in
  run_once (init true spec entry v) pause_handler
