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

(* The state of the interpreter *)

open Parsing
open Typing
open Anfscf
open Interpreter_common
open State_common
open Values
open Internal_errors
open Runtime_exceptions
open Interpreter_errors

(* Variable bindings *)
module Bindings = Map.Make(struct type t = Anf_common.varid
                                  let compare = compare
                           end)

(* Variable environment *)
module VEnv = struct
  type vmap = (Values.value * Anf.var) Bindings.t

  (* use a flat environment for now: consume more memory to
     prioritize speed *)
  type t = vmap

  let empty = Bindings.empty

  let assign (t: t) (v: Anf.var) (vl: Values.value) : t =
    Bindings.add Anf.(v.v) (vl, v) t

  let lookup (t: t) (v: Anf_common.varid) (l: Location.t) : Values.value =
    match Bindings.find_opt v t with
      | None         -> interpret_error l (No_binding_for_read v)
      | Some (vl, _) -> vl

  let bound (t: t) (v: Anf_common.varid) : bool =
    Bindings.mem v t

  let remove (t: t) (v: Anf_common.varid) : t =
    assert (bound t v);
    Bindings.remove v t
end

(* Function environment *)
module FEnv = struct
  type t = (Anf.var * Anf.var list * Anf.aexp) Bindings.t

  let empty = Bindings.empty

  let assign (t: t) (fv: Anf.var) (params: Anf.var list) (b: Anf.aexp)
      : t =
    if   Bindings.mem (Anf.(fv.v)) t
    then let fs = Anf_common.string_of_var fv.v in
         let err = Duplicate_function_binding fs in
         interpret_error fv.v_loc  err
    else Bindings.add Anf.(fv.v) (fv, params, b) t

  let lookup (t: t) (v: Anf_common.varid) (l: Location.t)
      : (Anf.var list * Anf.aexp) =
    match Bindings.find_opt v t with
      | None             -> interpret_error l (No_binding_for_read v)
      | Some (_, ps, bd) -> ps, bd
end

(* Module value environment *)
module ModBindings = Map.Make(struct type t = string * string
                                     let compare = compare
                              end)
module MVEnv = struct
  type t = (Values.value * Location.t) ModBindings.t

  let empty = ModBindings.empty

  let assign (t: t) (mv: ModBindings.key) (vl: Values.value) (l: Location.t)
      : t =
    if   ModBindings.mem mv t
    then let m, v = mv in
         let err  = Duplicate_mod_value_binding (m, v) in
         interpret_error l err
    else ModBindings.add mv (vl, l) t

  let lookup (t: t) (mv: ModBindings.key) (l: Location.t)
      : Values.value =
    match ModBindings.find_opt mv t with
      | Some (vl, _) -> vl
      | None         -> let m, v = mv in
                        let err = No_mod_binding_for_read (m, v) in
                        interpret_error l err
end

(* Module function environment *)
module MFEnv = struct
  type t = (Anf.var list * Anf.aexp) ModBindings.t

  let empty = ModBindings.empty

  let assign (t: t) (fv: ModBindings.key) (params: Anf.var list) (b: Anf.aexp)
        (l: Location.t) : t =
    if   ModBindings.mem fv t
    then let m, v = fv in
         let err = Duplicate_mod_value_binding (m, v) in
         interpret_error l err
    else ModBindings.add fv (params, b) t

  let lookup (t: t) (fv: ModBindings.key) (l: Location.t)
      : (Anf.var list * Anf.aexp) =
    match ModBindings.find_opt fv t with
      | Some (ps, bd) -> ps, bd
      | None          -> let m, v = fv in
                         let err = No_mod_binding_for_read (m, v) in
                         interpret_error l err
end

(* Choice frame, to save the environment and view stack at the
   beginning of a `start-choice`.  It is used for state restoration by
   `continue-choice` and dropped by `finish-choice` and `fail-choice`. *)
type choice_frame =
  {chf_venv:       VEnv.t;
   chf_start_view: Values.view;
   chf_view_stk:   Values.view list}

(* Control stack frame, set up/pushed by `N_call_nonterm` and
   used/popped on exit (via success or failure). *)
type call_frame =
  {cf_nt:          Ast.ident;                     (* (user-defined) non-terminal being called *)
   cf_nt_retvar:   Anf.var;                       (* variable for successful match *)
   cf_call_retvar: Anf.var;                       (* return variable for this call *)
   cf_call_cont:   Scf_context.zscf;              (* continuation *)
   cf_call_state:  state;                         (* call state *)
   cf_choice_stk:  choice_frame list}             (* choice context *)

and state =
  {(* static state *)
   st_spec_nts:     Scf.nt_entry Scf.ValueMap.t;
   (* static state only for debugging *)
   st_scf_tenv:     TypingEnvironment.environment;
   st_scf_venv:     Anf.VEnv.t;
   (* dynamic state *)
   st_mode:         mode;
   st_venv:         VEnv.t;
   st_fenv:         FEnv.t;
   st_mvenv:        MVEnv.t;
   st_mfenv:        MFEnv.t;
   st_view_stk:     Values.view list;  (* stack of views (minus top-of-stack) *)
   st_cur_view:     Values.view;       (* current view (top-of-view-stack) *)
   st_ctrl_stk:     call_frame list}

(* helpers *)

(* Projector and injector between bitstate and the overall state. *)

let to_bitstate (s: state) : bitstate =
  {bs_mode     = s.st_mode;
   bs_cur_view = s.st_cur_view}

let from_bitstate (s: state) (bs: bitstate) : state =
  {s with st_mode     = bs.bs_mode;
          st_cur_view = bs.bs_cur_view}

(* Returns the `vu_ofs` and `vu_end` of the view in the state. *)
type last_pos = int * int
let view_info (s: state) : last_pos =
  let v = s.st_cur_view in
  v.vu_ofs, v.vu_end

let fmt_pos (p: last_pos) : string =
  let o, e = p in
  Printf.sprintf "offset %d (%d bytes remaining)" o (e - o)

let get_ntentry (s: state) ((m, nt): Anf_common.modul * Ast.ident) : Scf.nt_entry =
  let ntn = Location.value nt in
  match Scf.ValueMap.find_opt (m, ntn) s.st_spec_nts with
    | None ->
        let err = Interpreter_errors.No_nonterm_entry nt in
        Interpreter_errors.interpret_error (Location.loc nt) err
    | Some ent ->
        ent

(* An error in looking up the entry non-terminal is not an internal
   error. *)
let get_init_ntentry (s: state) (nt: Anf_common.modul * string) : Scf.nt_entry option =
  Scf.ValueMap.find_opt nt s.st_spec_nts

(* Set current view. *)

let set_view lc (s: state) (v: value) : state =
  match v with
    | V_view vu ->
        {s with st_cur_view = vu}
    | _ ->
        internal_error lc (Type_error ("set-view", 1, vtype_of v, T_view))

let set_pos lc (s: state) (v: value) : state =
  (* Extend view before bounds checks. *)
  extend_view s.st_cur_view;
  match v with
    | V_int (ti, i) when ti = Ast.usize_t ->
        let i = Int64.to_int i in
        let vu = s.st_cur_view in
        if   i < 0
        then fault lc (View_bound ("set-pos", "negative offset specified"))
        else if vu.vu_start + i >= vu.vu_end
        then fault lc (View_bound ("set-pos", "end bound exceeded"))
        else let vu = {vu with vu_ofs = vu.vu_start + i} in
             {s with st_cur_view = vu}
    | _ ->
        internal_error lc (Type_error ("set-pos", 1, vtype_of v, T_int Ast.usize_t))

(* Suspend/resume handling. *)

type pause_reason =
  (* The backing buffer of the specified `view` needs the specified
     number of bytes to be appended to the end of the parse buffer.
     Since the view contains a pointer indirection to the buffer, no
     variable bindings to the view need to be updated. *)
  | Paused_require_refill of Values.view * int

(* Helpers to manipulate the choice stack: create a choice frame (on
   start-choices), restore from a choice frame (on continue-choice or
   fail-choice), pop a choice frame (on fail-choice or
   finish-choice). *)

let create_choice_frame (s: state) : state =
  let chf = {chf_venv       = s.st_venv;
             chf_start_view = s.st_cur_view;
             chf_view_stk   = s.st_view_stk} in
  (* TODO: convert exceptions here to internal errors. *)
  let cthd, cttl = List.hd s.st_ctrl_stk, List.tl s.st_ctrl_stk in
  let cthd = {cthd with cf_choice_stk = chf :: cthd.cf_choice_stk} in
  {s with st_ctrl_stk = cthd :: cttl}

let restore_choice (s: state) : state =
  (* TODO: convert exceptions here to internal errors. *)
  let cthd = List.hd s.st_ctrl_stk in
  let chf  = List.hd cthd.cf_choice_stk in
  {s with st_venv     = chf.chf_venv;
          st_cur_view = chf.chf_start_view;
          st_view_stk = chf.chf_view_stk}

let pop_choice_frame (s: state) : state =
  (* TODO: convert exceptions here to internal errors. *)
  let cthd, cttl = List.hd s.st_ctrl_stk, List.tl s.st_ctrl_stk in
  let cthd = {cthd with cf_choice_stk = List.tl cthd.cf_choice_stk} in
  {s with st_ctrl_stk = cthd :: cttl}
