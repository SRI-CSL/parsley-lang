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
open Ir
open Runtime_exceptions
open Internal_errors

(* bit-level parsing state *)

type bitwise =
  {bw_bit_ofs: int;
   bw_view:    Values.view; (* view to rewind to on failure *)
   bw_matched: bool list}

type mode =
  | Mode_normal
  | Mode_bitwise of bitwise

(* Variable bindings *)
module Bindings = Map.Make(struct type t = Anf.varid
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

  let lookup (t: t) (v: Anf.varid) (l: Location.t) : Values.value =
    match Bindings.find_opt v t with
      | None         -> internal_error l (No_binding_for_read v)
      | Some (vl, _) -> vl

  let bound (t: t) (v: Anf.varid) : bool =
    Bindings.mem v t
end

(* Function environment *)
module FEnv = struct
  type t = (Anf.var * Anf.var list * Anf.aexp) Bindings.t

  let empty = Bindings.empty

  let assign (t: t) (fv: Anf.var) (params: Anf.var list) (b: Anf.aexp)
      : t =
    if   Bindings.mem (Anf.(fv.v)) t
    then let fs = Anf_printer.string_of_var fv.v in
         let err = Duplicate_function_binding fs in
         internal_error fv.v_loc  err
    else Bindings.add Anf.(fv.v) (fv, params, b) t

  let lookup (t: t) (v: Anf.varid) (l: Location.t)
      : (Anf.var list * Anf.aexp) =
    match Bindings.find_opt v t with
      | None             -> internal_error l (No_binding_for_read v)
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
         internal_error l err
    else ModBindings.add mv (vl, l) t

  let lookup (t: t) (mv: ModBindings.key) (l: Location.t)
      : Values.value =
    match ModBindings.find_opt mv t with
      | Some (vl, _) -> vl
      | None         -> let m, v = mv in
                        let err = No_mod_binding_for_read (m, v) in
                        internal_error l err
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
         internal_error l err
    else ModBindings.add fv (params, b) t

  let lookup (t: t) (fv: ModBindings.key) (l: Location.t)
      : (Anf.var list * Anf.aexp) =
    match ModBindings.find_opt fv t with
      | Some (ps, bd) -> ps, bd
      | None          -> let m, v = fv in
                         let err = No_mod_binding_for_read (m, v) in
                         internal_error l err
end

(* Control stack entry, set up/pushed by `N_call_nonterm` and
   used/popped by `N_return`. *)
type call_frame =
  {cf_nt:          Ast.ident;                     (* (user-defined) non-terminal being called *)
   cf_conts:       (Cfg.label* Cfg.label) option; (* success/fail continuations for return *)
   cf_nt_retvar:   Anf.var;                       (* variable for successful match *)
   cf_call_retvar: Cfg.return;                    (* (optional) return variable for this call *)
   cf_call_state:  state;                         (* call state *)
   cf_nt_succcont: Cfg.label;                     (* continuations for call *)
   cf_nt_failcont: Cfg.label}                     (*   (sanity check only)  *)

and state =
  {(* static state *)
   st_spec_toc:     Cfg.nt_entry Cfg.ValueMap.t;
   st_spec_ir:      Cfg.closed Cfg.LabelMap.t;
   (* static state only for debugging *)
   st_ir_tenv:      TypingEnvironment.environment;
   st_ir_venv:      Anf.VEnv.t;
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

let get_block lc (s: state) (l: Cfg.label) : Cfg.closed =
  (* We should only be given static labels. *)
  assert (Cfg.is_static l);
  let l = Cfg.raw_label_of l in
  match Cfg.LabelMap.find_opt l s.st_spec_ir with
    | Some b ->
        b
    | None ->
        let err = Internal_errors.No_block_for_label l in
        internal_error lc err

let get_ntentry (s: state) ((m, nt): Anf.modul * Ast.ident) : Cfg.nt_entry =
  let ntn = Location.value nt in
  match Cfg.ValueMap.find_opt (m, ntn) s.st_spec_toc with
    | None ->
        let err = Internal_errors.No_nonterm_entry nt in
        internal_error (Location.loc nt) err
    | Some ent ->
        ent

(* An error in looking up the entry non-terminal is not an internal
   error. *)
let get_init_ntentry (s: state) (nt: Anf.modul * string) : Cfg.nt_entry option =
  Cfg.ValueMap.find_opt nt s.st_spec_toc
