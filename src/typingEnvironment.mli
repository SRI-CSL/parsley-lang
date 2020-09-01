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

(** [TypingEnvironment] implements two mappings used during the constraint
    generation.
    The first one associates a kind, a flexible variable and an optional
    list of data constructors to a type name.
    The second one records the scheme of the data constructors. *)

(** An algebraic datatype is characterized by a list of data constructors. *)
type algebraic_datatype = (Ast.dname * MultiEquation.variable) list

(** A type is characterized by a kind, a variable and an optional set of
    algebraic data constructors. *)
type type_info =
    KindInferencer.t * MultiEquation.variable * algebraic_datatype option ref

(** A data constructor's type is denoted by an ML scheme. *)
type data_constructor =
    int * MultiEquation.variable list * MultiEquation.crterm

(** The type of the typing environement. *)
type environment

(** The empty environment. *)
val empty_environment : environment

(** [fold_type_info] folds over the environment focusing on type's
    information. *)
val fold_type_info:
  ('a -> (Ast.tname * type_info) -> 'a) -> 'a -> environment -> 'a

(** Add a set of type variables into the environment, associating a
    name to each. *)
val add_type_variables: (Ast.tname * type_info) list -> environment -> environment

(** Add a type constructor into the environment. *)
val add_type_constructor: environment -> Ast.tname -> type_info -> environment

(** Add a data constructor into the environment. *)
val add_data_constructor:
  environment -> Ast.dname -> data_constructor -> environment

(** [is_regular_datacon_scheme env adt_name vs ty] checks that forall vs.ty is
    a valid scheme for a data constructor; that is to say, following the
    shape:
    K :: forall a1 .. an. tau_1 -> ... -> tau_n -> adt_name a1 ... an *)
val is_regular_datacon_scheme: environment -> Ast.tname -> MultiEquation.variable list -> MultiEquation.crterm -> bool

(** [lookup_datacon env k] gives access to the typing information
    related to the data constructor [k] in [env]. *)
val lookup_datacon :
  ?pos:Location.t -> environment -> Ast.dname -> data_constructor

(** Looks for a type constructor given its name. *)
val lookup_type_variable :
  ?pos:Location.t -> environment -> Ast.tname -> MultiEquation.variable CoreAlgebra.arterm

(** Accessor to the kind of a type. *)
val typcon_kind : environment -> Ast.tname -> KindInferencer.t

(** Accessor to the unification variable of a type. *)
val typcon_variable : environment -> Ast.tname -> MultiEquation.variable CoreAlgebra.arterm

(** [as_fun env] provides a view of [env] as function from names to
    variable. This is used to abstract the environment when it is
    given to the {!TypeAlgebra} module
    (see {!TypeAlgebra.type_of_primitive} for instance). *)
val as_fun : environment -> (Ast.tname -> MultiEquation.variable CoreAlgebra.arterm)

(** [as_kind env] provides a view of [env] as kind environment. *)
val as_kind_env : environment ->
  (Ast.tname -> KindInferencer.t) * (Ast.tname -> KindInferencer.t -> unit)

(** [fresh_datacon_scheme env dname vs] retrieves the type scheme
    of [dname] in [env] and alpha convert it using [vs] as a set
    of names to use preferentially when printing. *)
val fresh_datacon_scheme :
  Location.t -> environment -> Ast.dname -> (MultiEquation.variable list * MultiEquation.crterm)

(** [fresh_flexible_vars pos env vs] returns a list of fresh flexible
    variables whose visible names are [vs] and an environment fragment. *)
val fresh_flexible_vars :
  Location.t -> environment -> Ast.tname list ->
  MultiEquation.variable list * (Ast.tname * type_info) list

(** [fresh_flexible_vars pos env vs] returns a list of fresh rigid
    variables whose visible names are [vs] and an environment fragment. *)
val fresh_rigid_vars :
  Location.t -> environment -> Ast.tname list ->
  MultiEquation.variable list * (Ast.tname * type_info) list

(** [fresh_flexible_vars pos env] returns a list of fresh rigid
    variables without visible names and an environment fragment. *)
val fresh_unnamed_rigid_vars :
  Location.t -> environment -> 'a list -> MultiEquation.variable list * ('a * type_info) list
