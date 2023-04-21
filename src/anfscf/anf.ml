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
open Site

(* The IR for the expression language is the A-normal form.

   The design of the variable representation is shared with the
   grammar language, which incorporates mutation and backtracking.
   The book-keeping to support the latter tracks the frames in which
   variables are allocated.
 *)

(* Frame identifiers and their generation. *)

type frame_id = int
type frame_gen = unit -> frame_id

let mk_frame_id_gen () : frame_gen =
  let frm = ref 0 in
  fun () -> let id = !frm in
            incr frm;
            id

let str_of_frame_id (f: frame_id) =
  string_of_int f

module VSet = Set.Make(struct type t = varid * frame_id
                              let compare = compare
                       end)

module VMap = Map.Make(struct type t = varid * frame_id
                              let compare = compare
                       end)

module FieldSet = Set.Make(struct type t = string list
                                  let compare = compare
                           end)

(* variable bindings *)

type var =
  {v:       varid;
   v_typ:   typ;
   v_frame: frame_id;
   v_loc:   Location.t}

let mk_site_var v (k: site_var_type) (var: var) =
  {sv_ident = AstUtils.ident_of_var v;
   sv_type  = k;
   sv_var   = var.v}

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

let make_var v f t l =
  {v;
   v_typ   = t;
   v_frame = f;
   v_loc   = l}

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

(* An occurrence identifies the subterm of the value being scrutinized
   by a pattern.  The list starts from the root and goes towards
   the sub-term.  An empty list indicates the entire value.  Constructor
   arguments are numbered starting from 1. *)
type occurrence = int list
let root_occurrence = []

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
  | AE_bits_of_rec of av * (modul * Ast.ident * TypingEnvironment.bitfield_info)
  | AE_rec_of_bits of av * (modul * Ast.ident * TypingEnvironment.bitfield_info)
  | AE_bitrange of av * int * int
  | AE_match of av * (modul * string * string)
  | AE_field of av * Ast.ident
  | AE_case of av * (apat * aexp) list
  | AE_let of var * aexp * aexp
  | AE_cast of av * Ast.type_expr
  | AE_print of bool * av
  (* subterm identification for pattern variables *)
  | AE_letpat of var * (av * occurrence) * aexp

and aexp =
  {aexp:      aexp_desc;
   aexp_typ:  typ;
   aexp_loc:  Location.t;
   aexp_site: site option}

(* constructors for expressions *)

let make_ae ae t l s =
  {aexp      = ae;
   aexp_typ  = t;
   aexp_loc  = l;
   aexp_site = s}

let ae_of_av (av: av) : aexp =
  {aexp      = AE_val av;
   aexp_typ  = av.av_typ;
   aexp_loc  = av.av_loc;
   aexp_site = None}

type aconst =
  {aconst_var: var;
   aconst_val: aexp;
   aconst_mod: string;
   aconst_loc: Location.t}

type afun =
  {afun_ident:     var;
   afun_params:    var list;
   afun_body:      aexp;
   afun_site:      site;
   afun_vars:      VSet.t;   (* new vars bound in the body (not including params) *)
   afun_frame:     frame_id;
   afun_recursive: bool;
   afun_synth:     bool;
   afun_mod:       string;
   afun_loc:       Location.t}

type astmt_desc =
  | AS_set_var of var * aexp
  | AS_set_field of var * Ast.ident list * aexp
  | AS_print of bool * av
  | AS_let of var * aexp * astmt
  | AS_case of av * (apat * astmt) list
  | AS_block of astmt list
  (* subterm identification for pattern variables *)
  | AS_letpat of var * (av * occurrence) * astmt

and astmt =
  {astmt:      astmt_desc;
   astmt_loc:  Location.t;
   astmt_site: site option}

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
  val new_since: t -> t -> frame_id -> VSet.t
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

  let new_since ((c, binds) as _nu: t) ((c', _binds') as _old: t)
        (frame: frame_id) : VSet.t =
    assert (!c >= !c');
    Bindings.fold (fun (_: Bindings.key) ((_, cnt) as v) (s: VSet.t) ->
        if   cnt > !c'
        then VSet.add (v, frame) s
        else s
      ) (binds: varid Bindings.t) VSet.empty
end

(* Errors *)

type anf_error =
  | Unassignable_expression

exception Error of Location.t * anf_error

let error_msg = function
  | Unassignable_expression ->
      "The left side of this assignment is not assignable."

(* Normalization contexts.

   Expressions (and hence, function bodies) are purely functional and
   do not perform mutations, and their normalization requires a
   simpler context.

   When normalizing statements and actions, we need an extended
   context in order to accumulate (and verify) variables that are
   mutated.  This requires an extended context containing the frames
   in scope.  Statements and actions only occur within grammar rules,
   and hence their dynamic calling context will always have an
   invoking call to the non-terminal they are defining.  During that
   invocation, the dynamic frame context will always match the static
   context. [Proof?]

   For execution monitors, we collect the free variables in scope
   (indexed by string name).
 *)

type anf_exp_ctx =
  {anfe_tenv:      TypingEnvironment.environment;
   anfe_venv:      VEnv.t;
   anfe_frame:     frame_id;
   anfe_frame_gen: frame_gen;
   anfe_site_gen:  site_id_gen;
   anfe_site_map:  site SiteMap.t;
   anfe_free_vars: site_var StringMap.t}

(* mutated variables and fields *)

type mutations = FieldSet.t VMap.t

(* utility for combining mutations *)
let union_mutations (ma: mutations) (mb: mutations) =
  VMap.union (fun _ fs fs' ->
      Some (FieldSet.union fs fs')
    ) ma mb

type anf_stm_ctx =
  {anfs_tenv:      TypingEnvironment.environment;
   anfs_venv:      VEnv.t;
   anfs_frame:     frame_id;
   anfs_stack:     frame_id list;
   anfs_frame_gen: frame_gen;
   anfs_site_gen:  site_id_gen;
   anfs_site_map:  site SiteMap.t;
   anfs_free_vars: site_var StringMap.t;
   anfs_muts:      mutations}

(* The expression context is always a projection of the latest
   statement context. *)
let mk_exp_ctx (ctx: anf_stm_ctx) : anf_exp_ctx =
  {anfe_tenv      = ctx.anfs_tenv;
   anfe_venv      = ctx.anfs_venv;
   anfe_frame     = ctx.anfs_frame;
   anfe_frame_gen = ctx.anfs_frame_gen;
   anfe_site_gen  = ctx.anfs_site_gen;
   anfe_site_map  = ctx.anfs_site_map;
   anfe_free_vars = ctx.anfs_free_vars}

(* An expression context updates the statement context it was
 * derived from. *)
let fold_exp_ctx (sc: anf_stm_ctx) (ec: anf_exp_ctx) : anf_stm_ctx =
  (* Expression normalization does not modify the typing environment
   * or the current frame. *)
  assert (sc.anfs_frame = ec.anfe_frame);
  {sc with anfs_venv = ec.anfe_venv}
