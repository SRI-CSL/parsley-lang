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

(*  Adapted from:                                                         *)
(*  Mini, a type inference engine based on constraint solving.            *)
(*  Copyright (C) 2006. François Pottier, Yann Régis-Gianas               *)
(*  and Didier Rémy.                                                      *)

(** This module transforms types from the user's syntax to the
    internal representation of the inference engine. *)

open Misc
open TypeAlgebra
open MultiEquation
open TypingEnvironment
open TypingExceptions
open Ast

let rec extract_type e =
  match e.expr with
  | E_cast (exp, typ) ->
      Some (typ, exp)
  | _ ->
      None

(** {2 From user's syntax to internal term representation} *)

let variables_of_typ =
  let rec vtyp acu t =
    match t.type_expr with
    | TE_tvar (x) ->
        StringSet.add (Location.value x) acu
    | TE_tapp (t, ts) ->
        List.fold_left vtyp (vtyp acu t) ts
    | TE_record fields ->
        List.fold_left (fun acu pd ->
            let (_f, t) = Location.value pd in
            vtyp acu t
          ) acu fields
  in
    vtyp StringSet.empty

let arrow tenv =
  arrow (typcon_variable tenv)

let rec type_of_args t =
  let rec chop acu typ =
    match typ.type_expr with
    | TE_tapp ({type_expr = TE_tvar c}, [t1; t2])
         when Location.value c = "->" ->
        chop (t1 :: acu) t2
    | t ->
        acu
  in List.rev (chop [] t)

let arity t =
  List.length (type_of_args t)

let tycon tenv t =
  CoreAlgebra.app (lookup_type_variable tenv (TName (Location.value t)))

let rec intern' pos tenv t : crterm =
  match t.type_expr with

    | TE_tvar name ->
        as_fun tenv (TName (Location.value name))

    | TE_tapp (t, args) ->
        let iargs = List.map (intern' pos tenv) args in
          CoreAlgebra.app (intern' pos tenv t) iargs

    | TE_record fields ->
        (* TODO *)
        assert false

(** [intern tenv typ] converts the type expression [typ] to a type.
    The environment [tenv] maps type identifiers to types. *)
let rec intern pos tenv ty =
  let kind_env = as_kind_env tenv in
  let _ = KindInferencer.check pos kind_env ty KindInferencer.star in
    intern' pos tenv ty

let intern_let_env pos tenv rs fs =
  let fs = List.map AstUtils.to_tname fs in
  let rs = List.map AstUtils.to_tname rs in
  let fqs, rtenv = fresh_flexible_vars pos tenv fs in
  let rqs, rtenv' = fresh_rigid_vars pos tenv rs in
    rqs, fqs, add_type_variables (rtenv @ rtenv') tenv

(** [intern_scheme tenv name qs typ] produces a type scheme
    that binds [name] to [forall qs.typ]. *)
let intern_scheme pos tenv name qs typ =
  let qs = List.map AstUtils.to_tname qs in
  let fqs, rtenv = fresh_flexible_vars pos tenv qs in
    TypeConstraint.Scheme (pos, [], fqs, CTrue pos,
                           StringMap.singleton name
                         ((intern pos (add_type_variables rtenv tenv) typ),
                          pos))
