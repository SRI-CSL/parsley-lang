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

(* types generated by type-checking *)
type typ = MultiEquation.crterm

(* source level expressions *)
type exp = (typ, TypeInfer.varid) Ast.expr

(* source-level patterns *)
type pat = (typ, TypeInfer.varid) Ast.pattern

(* source-level functions *)
type func = (typ, TypeInfer.varid) Ast.fun_defn

(* source-level functions *)
type stmt = (typ, TypeInfer.varid) Ast.stmt

(* The IR for the expression language is the A-normal form. *)

type varid = string * int

(* variable bindings *)
type var =
  {v: varid;
   v_typ: typ;
   v_loc: Location.t}

(* values of ANF *)
type av_desc =
  | AV_lit of Ast.primitive_literal
  | AV_var of varid
  | AV_constr of (Ast.ident * Ast.ident) * av list
  | AV_record of (Ast.ident * av) list

and av =
  {av: av_desc;
   av_typ: typ;
   av_loc: Location.t}

(* pattern tags for switches *)
type apat_desc =
  | AP_wildcard
  | AP_literal of Ast.primitive_literal
  | AP_variant of (Ast.ident * Ast.ident)

and apat =
  {apat: apat_desc;
   apat_typ: typ;
   apat_loc: Location.t}

(* An occurrence identifies the subterm of the value being scrutinized
   by a pattern.  The list starts from the subterm and goes towards
   the root.  An empty list indicates the entire value.  Constructor
   arguments are numbered starting from 1.*)
type occurrence = int list

(* In the A-normal form, primitive operations are performed on
   `values' that are essentially names for evaluated subexpressions.
   As a result, evaluation of subexpressions takes place in let
   bindings that name the result, and the sequence of let bindings
   makes the sequence of computation explicit.
 *)
type aexp_desc =
  | AE_val of av
  | AE_apply of av * av list
  | AE_unop of Ast.unop * av
  | AE_binop of Ast.binop * av * av
  | AE_recop of Ast.ident * Ast.ident * av
  | AE_bitrange of av * int * int
  | AE_match of av * (Ast.ident * Ast.ident)
  | AE_field of av * Ast.ident
  | AE_mod_member of Ast.modident * Ast.ident
  | AE_case of var * (apat * aexp) list
  | AE_let of var * aexp * aexp
  | AE_cast of av * Ast.type_expr
  (* subterm identification for pattern variables *)
  | AE_letpat of var * (av * occurrence) * aexp

and aexp =
  {aexp: aexp_desc;
   aexp_typ: typ;
   aexp_loc: Location.t}

type afun =
  {afun_ident: varid;
   afun_params: varid list;
   afun_body: aexp;
   afun_recursive: bool;
   afun_loc: Location.t}

type astmt_desc =
  | AS_set_var of var * aexp
  | AS_set_field of var * Ast.ident * aexp
  | AS_let of var * aexp * astmt
  | AS_case of var * (apat * astmt) list
  | AS_block of astmt list
  (* subterm identification for pattern variables *)
  | AS_letpat of var * (av * occurrence) * astmt

and astmt =
  {astmt: astmt_desc;
   astmt_loc: Location.t}

(* variable generator for A-normal form *)

module Bindings = Map.Make(struct type t = string * TypeInfer.varid
                                  let compare = compare
                           end)
module VEnv : sig
  type t
  val empty: t
  val gen: t -> varid * t
  val bind: t -> TypeInfer.varid Ast.var -> varid * t
  val lookup: t -> TypeInfer.varid Ast.var -> varid
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
end

type anf_error =
  | Unassignable_expression of Location.t

exception Error of anf_error