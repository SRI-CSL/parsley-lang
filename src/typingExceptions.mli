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

(** This modules declares the exceptions raised by the type inference engine. *)

(** [UnboundTypeIdentifier] is raised when an unbound type identifier
    is found. *)
exception UnboundTypeIdentifier of Location.t * Ast.tname

(** [InvalidTypeVariableIdentifier] is raised when a type variable is
    overwriting a type constructor. *)
exception InvalidTypeVariableIdentifier of Location.t * Ast.tname

(** [UnboundDataConstructor] is raised when a constructor identifier is
  used although it has not been defined. *)
exception UnboundDataConstructor of Location.t * Ast.dname

(** [UnboundRecordField] is raised when a field label is
    used although it has not been defined. *)
exception UnboundRecordField of Location.t * Ast.lname

(** [InvalidDataConstructorDefinition] is raised when the declared
    type scheme of a data constructor is not regular. *)
exception InvalidDataConstructorDefinition of Location.t * Ast.dname

(** [InvalidFieldDestructorDefinition] is raised when a field destructor
    scheme is not legal. *)
exception InvalidFieldDestructorDefinition of Location.t * Ast.lname

(** [UnboundTypeVariable] is raised when a variable identifier is
    used although it has not been defined. *)
exception UnboundTypeVariable of Location.t * Ast.tname

(** [MultipleLabels] is raised when the user has built a record
    with two fields with the same name. *)
exception MultipleLabels of Location.t * Ast.lname

(** [NonLinearPattern] is raised when at least two occurrences of a variable
    appear in a pattern. *)
exception NonLinearPattern of Location.t * string

(** [InvalidDisjunctionPattern] is raised when the subpatterns of a
    disjunction pattern do not bind the same variables. *)
exception InvalidDisjunctionPattern of Location.t

(** [NotEnoughPatternArgts] is raised when the arity of a data constructor
    is not respected in a pattern. *)
exception NotEnoughPatternArgts of Location.t

(** [InvalidNumberOfTypeVariable] is raised when the introduction of
    existential type variables in a pattern is not well-formed. *)
exception InvalidNumberOfTypeVariable of Location.t

(** [RecursiveDefMustBeVariable] is raised in case of bad formed
    recursive value definition. *)
exception RecursiveDefMustBeVariable of Location.t

(** [CannotGeneralize] when the type of an expression cannot be
    generalized contrary to what is specified by the programmers
    using type annotations. *)
exception CannotGeneralize of Location.t * MultiEquation.crterm

(** [NonDistinctVariables] is raised when two rigid type variables have
    been unified. *)
exception NonDistinctVariables of Location.t * (MultiEquation.variable list)

(** [CannotUnifyHeadWithTerm] is raised when we encounter first order
    unification error. *)
exception CannotUnifyHeadWithTerm of Location.t * Ast.tname * MultiEquation.crterm

(** This exception is raised when a match is not complete. *)
exception NonExhaustiveMatch of Location.t * Ast.pattern

(** [UnboundConstructor] is raised when a type constructor is unbound. *)
exception UnboundTypeConstructor of Location.t * Ast.tname

(** [KindError] is raised when the kind of types are not correct. *)
exception KindError of Location.t

(** [PartialDataConstructorApplication] is raised when a data constructor's
    arity is not respected by the programmer. *)
exception PartialDataConstructorApplication of Location.t * int * int
