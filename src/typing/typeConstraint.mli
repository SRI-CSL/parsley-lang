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

(** This module manages a data structure for constraints in a multi-equation
    framework. *)

open Parsing
open Misc

(** [sname] is the type of the names that are used to refer to type
    schemes inside constraints. These names are bound by [CLet]
    constraints and referred to by [CInstance] constraints. *)
type sname = SName of string

(* TEMPORARY renommer en formula *)
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

(** The variables that appear in constraints are the same as the multi-equation
    ones. *)
type variable = MultiEquation.variable

(** The types in constraints are implemented using the internal data structure
    defined in {!CoreAlgebra}. The same data structure is also used in
    {!MultiEquation}. *)
type crterm = variable CoreAlgebra.arterm

(** Here is an abbreviation for the type constraint structure instantiated using
    our internal variable and term representations. *)
type tconstraint = (crterm, variable) type_constraint

(** Here is an abbreviation for the type scheme structure instantiated using
    out internal variable and term representations. *)
type tscheme = (crterm, variable) scheme

(** [cposition c] returns the position related to [c]. *)
val cposition : ('a, 'b) type_constraint -> Location.t

(** [t1 =?= t2] is an equality constraint *)
val (=?=): crterm -> crterm -> Location.t -> tconstraint

(** [ex qs c] returns the constraint [exists qs.c]. We encode existential
   constraints in terms of [let] constraints, since the latter are more
   general. *)
val ex : ?pos:Location.t -> variable list -> tconstraint -> tconstraint

(** [fl qs c] returns the constraint [forall qs.c]. We encode universal
   constraints in terms of [let] constraints, since the latter are more
   general. *)
val fl: ?pos:Location.t -> variable list -> tconstraint -> tconstraint

(** [x <? t] is an instance constraint. *)
val (<?): sname -> crterm -> Location.t -> tconstraint

(** [c1 ^ c2] is a conjunction constraint. *)
val (^): tconstraint -> tconstraint -> tconstraint

(** [conj cs] builds a conjunction between a list of constraints. *)
val conj: tconstraint list -> tconstraint

(** [exists f] creates a fresh variable [x] and returns the constraint
    [exists x.(f x)]. *)
val exists: ?pos:Location.t -> (crterm -> tconstraint) ->
            tconstraint
val exists_aux: ?pos:Location.t -> (crterm -> tconstraint * 'b) ->
            tconstraint * 'b

(** [exists_list l f] associates a fresh variable with every element
    in the list [l], yielding an association list [m], and returns
    the constraint [exists m.(f m)]. *)
val exists_list:
  ?pos:Location.t -> 'a list -> (('a * crterm) list -> tconstraint)
  -> tconstraint
val exists_list_aux:
  ?pos:Location.t -> 'a list -> (('a * crterm) list -> tconstraint * 'b)
  -> tconstraint * 'b
