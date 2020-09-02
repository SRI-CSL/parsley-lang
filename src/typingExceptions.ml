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

open Ast
open MultiEquation

(** This module provides the typing exceptions for the Mini language. *)
(** {2 Exceptions} *)

(** [UnboundTypeIdentifier] is raised when an unbound type identifier
    is found. *)
exception UnboundTypeIdentifier of Location.t * tname

(** [InvalidTypeVariableIdentifier] is raised when a type variable is
      overwriting a type constructor. *)
exception InvalidTypeVariableIdentifier of Location.t * tname

(** [UnboundDataConstructor] is raised when a constructor identifier is
    used although it has not been defined. *)
exception UnboundDataConstructor of Location.t * dname

(** [UnboundRecordField] is raised when a field label is
    used although it has not been defined. *)
exception UnboundRecordField of Location.t * lname

(** [InvalidDataConstructorDefinition] is raised when a data constructor
    scheme is not legal. *)
exception InvalidDataConstructorDefinition of Location.t * dname

(** [InvalidFieldDestructorDefinition] is raised when a field destructor
    scheme is not legal. *)
exception InvalidFieldDestructorDefinition of Location.t * lname

(** [UnboundTypeVariable] is raised when a variable identifier is
    used although it has not been defined. *)
exception UnboundTypeVariable of Location.t * tname

(** [MultipleLabels] is raised when the user has built a record
    with two fields with the same name. *)
exception MultipleLabels of Location.t * lname

(** [NonLinearPattern] is raised when at least two occurrences of a variable
    appear in a pattern. *)
exception NonLinearPattern of Location.t * string

exception NotEnoughPatternArgts of Location.t

exception InvalidNumberOfTypeVariable of Location.t

(** This exception is raised by [unify] when a system of equations
    is found to be unsatisfiable. *)
exception CannotUnifyHeadWithTerm of Location.t * tname * crterm

(** [CannotGeneralize] when the type of an expression cannot be
    generalized contrary to what is specified by the programmers
    using type annotations. *)
exception CannotGeneralize of Location.t * crterm

exception NonDistinctVariables of Location.t * (variable list)

(** This exception is raised when a match is not complete. *)
exception NonExhaustiveMatch of Location.t * pattern

exception UnboundIdentifier of Location.t * tname

exception UnboundTypeConstructor of Location.t * tname

exception KindError of Location.t

(** [RecursiveDefMustBeVariable] is raised in case of bad formed
    recursive value definition. *)
exception RecursiveDefMustBeVariable of Location.t

(** [InvalidDisjunctionPattern] is raised when the subpatterns of a
    disjunction pattern do not bind the same variables. *)
exception InvalidDisjunctionPattern of Location.t

(** [PartialDataConstructorApplication] is raised when a data constructor's
    arity is not respected by the programmer. *)
exception PartialDataConstructorApplication of Location.t * int * int
