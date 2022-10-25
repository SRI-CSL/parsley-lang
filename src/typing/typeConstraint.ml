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

open Parsing
open MultiEquation
open CoreAlgebra

module StringMap = Misc.StringMap

(** [sname] is the type of the names that are used to refer to type
    schemes inside constraints. These names are bound by [CLet]
    constraints and referred to by [CInstance] constraints. *)
type sname = SName of string

(** [type_constraint] defines a syntax for the constraints between
    types. *)
type ('crterm, 'variable) type_constraint =
  | CTrue of Location.t
  | CDump of Location.t
  | CEquation of Location.t * 'crterm * 'crterm
  | CConjunction of ('crterm, 'variable) type_constraint list
  | CLet of ('crterm, 'variable) scheme list
      * ('crterm, 'variable) type_constraint
  | CInstance of Location.t * sname * 'crterm

(** A type scheme is a pair of a constraint [c] and a header [h],
    wrapped within two sets of universal quantifiers [rqs] and
    [fqs]. The former are considered rigid, while the latter are
    considered flexible. More precisely, for the type scheme to be
    considered consistent, the constraint [forall rqs.exists fqs.c]
    must hold. Rigid and flexible quantifiers otherwise play the same
    role, that is, they all end up universally quantified in the type
    scheme. A header is a mapping of names to types. *)
and ('crterm, 'variable) scheme =
  | Scheme of Location.t * 'variable list * 'variable list
      * ('crterm, 'variable) type_constraint * ('crterm * Location.t) StringMap.t

type variable = MultiEquation.variable

type crterm =
    variable arterm

type tconstraint =
    (crterm, variable) type_constraint

type tscheme =
    (crterm, variable) scheme

let rec cposition = function
  | CTrue pos ->
      pos

  | CDump pos ->
      pos

  | CLet ([], c) ->
      cposition c

  | CConjunction [] ->
      Location.ghost_loc

  | CConjunction l ->
      Location.extent (cposition (List.hd l)) (cposition (Misc.last l))

  | CLet (l, _) ->
      Location.extent (sposition (List.hd l)) (sposition (Misc.last l))

  | CEquation (p, _, _) ->
      p

  | CInstance (p, _, _) ->
      p

and sposition = function
  | Scheme (p, _, _, _, _) ->
      p

(* TEMPORARY expliquer qu' on emploie la pile native pour les let
   et conj. frames, plus des pools s'epar'es pour les let frames *)

(** [x <? t] is an instance constraint. *)
let (<?) x t pos =
  CInstance (pos, x, t)

(** [t1 =?= t2] is an equality constraint. *)
let (=?=) t1 t2 pos =
  CEquation (pos, t1, t2)

(** [c1 ^ c2] is a conjunction constraint. *)
let (^) c1 c2 =
  match c1, c2 with
    | CTrue _, c
    | c, CTrue _ ->
      c
    | c, CConjunction cl ->
        CConjunction (c :: cl)
    | _, _ ->
        CConjunction [c1; c2]

let conj cs =
  List.fold_left ( ^ ) (CTrue Location.ghost_loc) cs

(** [ex qs c] returns the constraint [exists qs.c]. We encode existential
   constraints in terms of [let] constraints, since the latter are more
   general. *)
let ex ?pos qs c =
  CLet ([ Scheme (Location.loc_or_ghost pos, [], qs, c, StringMap.empty) ],
        CTrue (Location.loc_or_ghost pos))

(** [fl qs c] returns the constraint [forall qs.c]. We encode universal
   constraints in terms of [let] constraints, since the latter are more
   general. *)
let fl ?pos qs c =
  CLet ([ Scheme (Location.loc_or_ghost pos, qs, [], c, StringMap.empty) ],
        CTrue (Location.loc_or_ghost pos))

(** [exists f] creates a fresh variable [v] and returns the constraint
    [exists v.(f v)]. *)
let exists ?pos f =
  let v = variable Flexible () in
  let c = f (TVariable v) in
  ex ~pos:(Location.loc_or_ghost pos) [ v ] c

let exists_aux ?pos f =
  let v = variable Flexible () in
  let c, aux = f (TVariable v) in
  (ex ~pos:(Location.loc_or_ghost pos) [ v ] c), aux

(** [exists_list l f] associates a fresh variable with every element
    in the list [l], yielding an association list [m], and returns
    the constraint [exists m.(f m)]. *)
let exists_list ?pos l f =
  let l, m = variable_list Flexible l in
  ex ?pos:pos l (f m)

let exists_list_aux ?pos l f =
  let l, m = variable_list Flexible l in
  let c, aux = f m in
  ex ?pos:pos l c, aux

(** [forall_list l f] associates a fresh variable with every element
    in the list [l], yielding an association list [m], and returns
    the constraint [forall m.(f m)]. *)
let _forall_list ?pos l f =
  let l, m =
    List.fold_right (fun x (vs, xts) ->
                       let v = variable Rigid ~name:x () in
                         v :: vs, (x, TVariable v) :: xts
                    ) l ([], [])
  in
  fl ~pos:(Location.loc_or_ghost pos) l (f m)

(** [monoscheme header] turns [header] into a monomorphic type scheme. *)
let _monoscheme ?pos header =
  Scheme (Location.loc_or_ghost pos, [], [],
          CTrue (Location.loc_or_ghost pos), header)

(* constraints on bitvector widths *)

type width_predicate =
  | WP_less of int
  | WP_more of int
  | WP_equal of int
  | WP_less_eq of int
  | WP_more_eq of int

type width_constraint =
  | WC_true
  | WC_pred of Location.t * variable * width_predicate
  | WC_conjunction of width_constraint list

(** [c1 @^ c2] is a conjunction constraint. *)
let (@^) c1 c2 =
  match c1, c2 with
    | WC_true, c
    | c, WC_true ->
      c
    | c, WC_conjunction cl ->
        WC_conjunction (c :: cl)
    | _, _ ->
        WC_conjunction [c1; c2]

let wconj cs =
  List.fold_left ( @^ ) WC_true cs
