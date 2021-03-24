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

open Parsing
open Misc
open TypeAlgebra
open MultiEquation
open TypingEnvironment
open Ast

(** {2 From user's syntax to internal term representation} *)

let variables_of_typ =
  let rec vtyp acu t =
    match t.type_expr with
    | TE_tvar (x) ->
        let loc = Location.loc x in
        StringMap.add (Location.value x) loc acu
    | TE_tapp (t, ts) ->
        List.fold_left vtyp (vtyp acu t) ts
  in
    vtyp StringMap.empty

let arrow tenv =
  arrow (typcon_variable tenv)

let type_of_args t =
  let rec chop acu typ =
    match typ.type_expr with
    | TE_tapp ({type_expr = TE_tvar c; _}, [t1; t2])
         when Location.value c = "->" ->
        chop (t1 :: acu) t2
    | _ ->
        acu
  in List.rev (chop [] t)

let arity t =
  List.length (type_of_args t)

let tycon tenv t =
  CoreAlgebra.app (lookup_type_variable tenv (TName (Location.value t)))

let rec intern' tenv t : crterm =
  match t.type_expr with
    | TE_tvar name ->
        as_fun tenv (TName (Location.value name))
    | TE_tapp (t, args) ->
        let iargs = List.map (intern' tenv) args in
          CoreAlgebra.app (intern' tenv t) iargs

(** [intern tenv typ] converts the type expression [typ] to a type.
    The environment [tenv] maps type identifiers to types. *)
let intern tenv ty =
  let kind_env = as_kind_env tenv in
  let _ = KindInferencer.check kind_env ty KindInferencer.star in
    intern' tenv ty

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
                         ((intern (add_type_variables rtenv tenv) typ),
                          pos))
