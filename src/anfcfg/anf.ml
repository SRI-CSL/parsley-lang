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
open TypedAst
open Anf_common

(* The IR for the expression language is the A-normal form. *)

module VSet = Set.Make(struct type t = varid
                              let compare = compare
                       end)

(* variable bindings *)
type var =
  {v:     varid;
   v_typ: typ;
   v_loc: Location.t}

(* values of ANF *)

type av_desc =
  | AV_lit of Ast.primitive_literal
  | AV_var of varid
  | AV_constr of constr * av list
  | AV_record of (Ast.ident * av) list
  | AV_mod_member of Ast.modident * Ast.ident

and av =
  {av:     av_desc;
   av_typ: typ;
   av_loc: Location.t}

(* values in function position of an application *)
type fv_desc =
  | FV_var of varid
  | FV_mod_member of Ast.modident * Ast.ident

and fv =
  {fv:     fv_desc;
   fv_typ: typ;
   fv_loc: Location.t}

(* constructors for variables and values *)

let make_var v t l =
  {v;
   v_typ = t;
   v_loc = l}

let make_av v t l =
  {av     = v;
   av_typ = t;
   av_loc = l}

let av_of_var (v: var) : av =
  {av     = AV_var v.v;
   av_typ = v.v_typ;
   av_loc = v.v_loc}

let make_fv v t l =
  {fv     = v;
   fv_typ = t;
   fv_loc = l}

let fv_of_var (v: var) : fv =
  {fv     = FV_var v.v;
   fv_typ = v.v_typ;
   fv_loc = v.v_loc}

(* pattern tags for switches *)
type apat_desc =
  | AP_wildcard
  | AP_literal of Ast.primitive_literal
  | AP_variant of constr

and apat =
  {apat:     apat_desc;
   apat_typ: typ;
   apat_loc: Location.t}

(* In the A-normal form, primitive operations are performed on
   `values' that are essentially names for evaluated subexpressions.
   As a result, evaluation of subexpressions takes place in let
   bindings that name the result, and the sequence of let bindings
   makes the sequence of computation explicit.
 *)
type aexp_desc =
  | AE_val of av
  | AE_apply of fv * av list
  | AE_unop of Ast.unop * av
  | AE_binop of Ast.binop * av * av
  | AE_bits_of_rec of modul * Ast.ident * av * TypingEnvironment.bitfield_info
  | AE_rec_of_bits of modul * Ast.ident * av * TypingEnvironment.bitfield_info
  | AE_bitrange of av * int * int
  | AE_match of av * (modul * string * string)
  | AE_field of av * Ast.ident
  | AE_case of var * (apat * aexp) list
  | AE_let of var * aexp * aexp
  | AE_cast of av * Ast.type_expr
  | AE_print of bool * av
  (* subterm identification for pattern variables *)
  | AE_letpat of var * (av * occurrence) * aexp

and aexp =
  {aexp:     aexp_desc;
   aexp_typ: typ;
   aexp_loc: Location.t}

(* simplified module qualifiers *)

let modul_of_mname m =
  match m with
    | Ast.(Modul Mod_stdlib)       -> M_stdlib
    | Ast.(Modul (Mod_explicit m)) -> M_name (Location.value m)
    | Ast.(Modul (Mod_inferred m)) -> M_name m

let str_of_modul m =
  match m with
    | M_stdlib -> ""
    | M_name m -> m

let mod_prefix m s =
  match m with
    | M_stdlib -> s
    | M_name m -> Printf.sprintf "%s.%s" m s

let convert_con (m, t, c) =
  (modul_of_mname m), Location.value t, Location.value c

let string_of_constr ((m, t, c): constr) : string =
  mod_prefix m (AstUtils.canonicalize_dcon t c)

(* constructors for expressions *)

let make_ae ae t l =
  {aexp     = ae;
   aexp_typ = t;
   aexp_loc = l}

let ae_of_av (av: av) : aexp =
  {aexp     = AE_val av;
   aexp_typ = av.av_typ;
   aexp_loc = av.av_loc}

type aconst =
  {aconst_ident: varid;
   aconst_val:   aexp;
   aconst_mod:   string;
   aconst_loc:   Location.t}

type afun =
  {afun_ident:     var;
   afun_params:    var list;
   afun_body:      aexp;
   afun_vars:      VSet.t; (* new vars bound in the body (not including params) *)
   afun_recursive: bool;
   afun_synth:     bool;
   afun_mod:       string;
   afun_loc:       Location.t}

type astmt_desc =
  | AS_set_var of var * aexp
  | AS_set_field of var * Ast.ident list * aexp
  | AS_print of bool * av
  | AS_let of var * aexp * astmt
  | AS_case of var * (apat * astmt) list
  | AS_block of astmt list
  (* subterm identification for pattern variables *)
  | AS_letpat of var * (av * occurrence) * astmt

and astmt =
  {astmt:     astmt_desc;
   astmt_loc: Location.t}

module Bindings = Map.Make(struct type t = string * TypeInfer.varid
                                  let compare = compare
                           end)

(* variable generator for A-normal form: it ensures variables are
   globally unique.
 *)
module VEnv : sig
  type t
  val empty:     t
  val gen:       t -> varid * t
  val bind:      t -> TypeInfer.varid Ast.var -> varid * t
  val lookup:    t -> TypeInfer.varid Ast.var -> varid
  val is_bound:  t -> TypeInfer.varid Ast.var -> bool
  val new_since: t -> t -> VSet.t
end = struct
  type t = int ref * varid Bindings.t

  let empty =
    let count = ref 0 in
    count, Bindings.empty

  (* newly generated variables have no name and a unique counter *)
  let gen (count, binds) =
    incr count;
    ("", !count), (count, binds)

  let var_val (v: TypeInfer.varid Ast.var) : string * TypeInfer.varid =
    Location.value v

  (* existing variables retain their name but update their counter
     to a globally unique one *)
  let bind (count, binds) (var: TypeInfer.varid Ast.var) =
    incr count;
    let (n, _) as v = var_val var in
    let new_var = n, !count in
    let binds = Bindings.add v new_var binds in
    new_var, (count, binds)

  (* lookups should never fail, so this raises an uncaught [Not_found]
     on error *)
  let lookup (_, binds) (var: TypeInfer.varid Ast.var) =
    let v = var_val var in
    Bindings.find v binds

  (* checks if a variable has already been bound *)
  let is_bound (_, binds) (var: TypeInfer.varid Ast.var) =
    Bindings.mem (var_val var) binds

  let new_since ((c, binds): t) ((c', binds'): t) : VSet.t =
    assert (!c >= !c');
    Bindings.fold (fun k v s ->
        assert (Bindings.mem k binds);
        VSet.add v s
      ) binds' VSet.empty
end

type anf_error =
  | Unassignable_expression

exception Error of Location.t * anf_error

let error_msg = function
  | Unassignable_expression ->
      "The left side of this assignment is not assignable."
