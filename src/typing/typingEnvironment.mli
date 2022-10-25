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

open Parsing

(** [bitfield_info] tracks the fields and their bit index ranges of a
    bitfield.  The range for field `f` is represented as (f, hi, lo). *)
type bitfield_info =
  {bf_name:   string;
   bf_fields: (string * (int * int)) list;
   bf_length: int}

(** [record_info] tracks the field names, and the variables associated
    with their destructors and constructors *)
type record_info =
  {adt:                Ast.ident;
   modul:              Ast.mname;
   fields:             (Ast.ident * Ast.type_expr) list;
   record_constructor: Ast.tname * MultiEquation.variable;
   field_destructors:  (Ast.lname * MultiEquation.variable) list;
   bitfield_info:      bitfield_info option}

(** An algebraic datatype is characterized by a list of data
    constructors for variant types and field destructors for record types. *)
type algebraic_datatype =
  | Variant of (Ast.dname * MultiEquation.variable) list
  | Record of record_info

type adt_info =
  {adt: algebraic_datatype;
   loc: Location.t}

(** A type is characterized by a kind, a variable and an optional set of
    algebraic data constructors or destructors. *)
type type_info =
    KindInferencer.t * MultiEquation.variable * adt_info option ref

(** A data constructor's type is denoted by an ML scheme. *)
type data_constructor =
    int * MultiEquation.variable list * MultiEquation.crterm

(** A record's type is denoted by an ML scheme. *)
type record_constructor =
    MultiEquation.variable list * MultiEquation.crterm

(** A record field destructor's type is denoted by an ML scheme. *)
type field_destructor =
    MultiEquation.variable list * MultiEquation.crterm

(** A non-terminal's type definition *)
type non_term_inh_type =
  (MultiEquation.crterm * Location.t) Misc.StringMap.t
  * (int Ast.var * Ast.type_expr * MultiEquation.crterm) list
type non_term_syn_type =
  (* aliased to another type, either declared or inferred *)
  | NTT_type of MultiEquation.crterm * record_info option
  (* a monomorphic record of its synthesized attributes *)
  | NTT_record of MultiEquation.variable * record_info option ref
type non_term_type = non_term_inh_type * non_term_syn_type

(** A type abbreviation *)
type type_abbrev = {type_abbrev_tvars: Ast.tname list;
                    type_abbrev_type:  Ast.type_expr}

(** The type of the typing environement. *)
type environment

(** The empty environment. *)
val empty_environment: environment

(** [fold_type_info] folds over the environment focusing on type's
    information. *)
val fold_type_info:
  (Ast.full_tname -> type_info -> 'a -> 'a) -> 'a -> environment -> 'a

(** Add a set of type variables into the environment, associating a
    name to each. *)
val add_type_variables: (Ast.full_tname * type_info) list -> environment -> environment

(** Add a type abbreviation into the environment. *)
val add_type_abbrev:
  environment -> Location.t -> Ast.full_tname -> type_abbrev -> environment

(** Add a type constructor into the environment. *)
val add_type_constructor: environment -> Location.t -> Ast.full_tname -> type_info -> environment

(** Add a data constructor for an ADT into the environment. *)
val add_data_constructor:
  environment -> Location.t -> Ast.full_tname -> Ast.dname -> data_constructor -> environment

(** Add a constructor for a record ADT into the environment. *)
val add_record_constructor:
  environment -> Ast.full_tname -> record_constructor -> environment

(** Add a field destructor for an ADT into the environment. *)
val add_field_destructor:
  environment -> Location.t -> Ast.full_tname -> Ast.full_lname -> field_destructor -> environment

(** Add the type definition for a non-terminal into the environment. *)
val add_non_terminal:
  environment -> Location.t -> Ast.full_nname -> non_term_type -> environment

(** Add a expression module value binding for [mname.vname] with type
    [forall a1 .. an . tau] and foreign flag into the environment. *)
val add_value:
  environment -> Location.t -> Ast.full_vname ->
  (MultiEquation.variable list * MultiEquation.crterm) -> bool -> environment

(** [is_regular_datacon_scheme env adt_name vs ty] checks that forall vs.ty is
    a valid scheme for a data constructor; that is to say, following the
    shape:
    K :: forall a1 .. an. tau_1 -> ... -> tau_n -> adt_name a1 ... an *)
val is_regular_datacon_scheme: environment -> Ast.full_tname -> MultiEquation.variable list -> MultiEquation.crterm -> bool

(** [is_regular_field_scheme env adt_name vs ty] checks that forall vs.ty is
    a valid scheme for a record field destructor; that is to say, following the
    shape:
    K :: forall a1 .. an. adt_name a1 ... an -> tau_1 -> ... -> tau_n *)
val is_regular_field_scheme: environment -> Ast.full_tname -> MultiEquation.variable list -> MultiEquation.crterm -> bool

(** [is_{defined,variant,record}_type env t] checks whether the type
    with name [t] is defined in [env] and of the appropriate type. *)
val is_defined_type: environment -> Ast.full_tname -> bool
val is_variant_type: environment -> Ast.full_tname -> bool
val is_record_type:  environment -> Ast.full_tname -> bool
(* a more informative version of [is_record_type] *)
val get_record_info: environment -> Ast.full_tname -> record_info option

(** [lookup_adt env t] gives access to the typing information for the
    type with name [t]. *)
val lookup_adt: environment -> Ast.full_tname -> adt_info option

(** [lookup_type_abbrev env t] returns a type abbreviation if present
    in the environment. *)
val lookup_type_abbrev: environment -> Ast.full_tname -> type_abbrev option

(** [lookup_datacon env k] gives access to the typing information
    related to the data constructor [k] in [env]. *)
val lookup_datacon:
  environment -> Location.t -> Ast.full_dname -> data_constructor

(** [lookup_record_con env adt] gives access to the record constructor
    type of [adt] in [env]. *)
val lookup_record_constructor:
  environment -> Location.t -> Ast.full_tname -> record_constructor

(** [lookup_field_destructor env f] gives access to the typing
    information for the destructor of the record field [f] in [env]. *)
val lookup_field_destructor:
  environment -> Location.t -> Ast.full_lname -> field_destructor

(** [lookup_datacon_adt env k] returns the name of the ADT associated
    with the data constructor [k] in [env], if any. *)
val lookup_datacon_adt:
  environment -> Ast.full_dname -> Ast.full_tname option

(** [lookup_field_adt env f] returns the name of the ADT associated
    with the data constructor [k] in [env], if any. *)
val lookup_field_adt:
  environment -> Ast.full_lname -> Ast.full_tname option

(** Looks up the type for a type constructor given its name. *)
val lookup_type_variable:
  ?pos:Location.t -> environment -> Ast.full_tname -> MultiEquation.crterm

(** Looks up the type for a module component, and whether it is foreign. *)
val lookup_value:
  Location.t -> environment -> Ast.full_vname
  -> (MultiEquation.variable list * MultiEquation.crterm) * bool

(** [lookup_non_term env nt] looks up the type information for a
    non-terminal [nt] in [env], if any. *)
val lookup_non_term:
  environment -> Ast.full_nname
  -> (non_term_inh_type * MultiEquation.crterm * non_term_syn_type) option

(** [lookup_non_term_type env nt] looks up the type for a
    non-terminal [nt] in [env], if any. *)
val lookup_non_term_type:
  environment -> Ast.full_nname -> MultiEquation.crterm option

(** Accessor to the unification variable of a type. *)
val typcon_variable: environment -> Ast.full_tname -> MultiEquation.crterm

(** [as_fun env] provides a view of [env] as function from names to
    variable. This is used to abstract the environment when it is
    given to the {!TypeAlgebra} module
    (see {!TypeAlgebra.type_of_primitive} for instance). *)
val as_fun: environment -> (Ast.full_tname -> MultiEquation.crterm)

(** [as_kind env] provides a view of [env] as kind environment. *)
val as_kind_env: environment ->
  (Ast.full_tname -> Location.t -> KindInferencer.t) * (Ast.full_tname -> KindInferencer.t -> unit)

(** [fresh_datacon_scheme env dname] retrieves the type scheme
    of data constructor [dname] in [env]. *)
val fresh_datacon_scheme:
  environment -> Location.t -> Ast.full_dname -> (MultiEquation.variable list * MultiEquation.crterm)

(** [fresh_field_destructor_scheme env fname] retrieves the type
    scheme of the record field destructor [fname] in [env]. *)
val fresh_field_destructor_scheme:
  environment -> Location.t -> Ast.full_lname -> (MultiEquation.variable list * MultiEquation.crterm)

(** [fresh_flexible_vars pos env] returns a list of fresh rigid
    variables without visible names and an environment fragment. *)
val fresh_unnamed_rigid_vars:
  Location.t -> environment -> 'a list -> MultiEquation.variable list * ('a * type_info) list
