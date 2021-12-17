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
open Flow
open Ir
open Runtime_exceptions
open Internal_errors

(* bit-level parsing state *)

type bitwise =
  {bw_bit_ofs: int;
   bw_view_id: Int64.t;
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

  (* See the explanation for `fresh` in ir/cfg.ml. *)
  let assign (t: t) (v: Anf.var) (fresh: bool) (vl: Values.value) : t =
    if   Bindings.mem (Anf.(v.v)) t
    then Bindings.add Anf.(v.v) (vl, v) t
    else if not fresh
    then internal_error (No_binding_for_write v)
    else Bindings.add Anf.(v.v) (vl, v) t

  let lookup (t: t) (v: Anf.varid) (l: Location.t) : Values.value =
    match Bindings.find_opt v t with
      | None         -> internal_error (No_binding_for_read (l, v))
      | Some (vl, _) -> vl
end

(* Function environment *)
module FEnv = struct
  type t = (Anf.var * Anf.var list * Anf.aexp) Bindings.t

  let assign (t: t) (fv: Anf.var) (params: Anf.var list) (b: Anf.aexp) : t =
    if   Bindings.mem (Anf.(fv.v)) t
    then let fs = Anf_printer.string_of_var fv.v in
         let err = Duplicate_function_binding (fv.v_loc, fs) in
         internal_error err
    else Bindings.add Anf.(fv.v) (fv, params, b) t

  let lookup (t: t) (v: Anf.varid) (l: Location.t)
      : (Anf.var list * Anf.aexp) =
    match Bindings.find_opt v t with
      | None         -> internal_error (No_binding_for_read (l, v))
      | Some (_, ps, bd) -> ps, bd
end

type state =
  {(* static state *)
   st_spec_toc:     Cfg.nt_entry Cfg.FormatGToC.t;
   st_spec_ir:      Cfg.closed Cfg.FormatIR.t;
   st_spec_re:      Dfa.re_env;
   (* static state only for debugging *)
   st_ir_tenv:         TypingEnvironment.environment;
   st_ir_venv:         Anf.VEnv.t;
   (* dynamic state *)
   st_mode:         mode;
   st_venv:         VEnv.t;
   st_fenv:         FEnv.t;
   st_failcont_stk: Label.label list;  (* stack of failconts *)
   st_view_stk:     Values.view list;  (* stack of views (minus top-of-stack) *)
   st_cur_view:     Values.view}       (* current view (top-of-view-stack) *)
