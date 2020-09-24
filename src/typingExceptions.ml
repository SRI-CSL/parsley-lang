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

(** This module declares the errors raised by the type inference engine. *)

type typing_error =
  (** [UnboundTypeIdentifier] is raised when an unbound type identifier
      is found. *)
  | UnboundTypeIdentifier of Location.t * Ast.tname

  (** [DuplicateTypeVariable] is raised when a type variable declaration
      is repeated in a type definition. *)
  | DuplicateTypeVariable of Ast.ident

  (** [UnusedTypeVariable] is raised when a type variable declaration
      is not used in a type definition. *)
  | UnusedTypeVariable of Ast.ident

  (** [InvalidTypeVariableIdentifier] is raised when a type variable is
      overwriting a type constructor. *)
  | InvalidTypeVariableIdentifier of Location.t * Ast.tname

  (** [UnboundDataConstructor] is raised when a constructor identifier is
      used although it has not been defined. *)
  | UnboundDataConstructor of Location.t * Ast.dname

  (** [DuplicateDataConstructor dc t] is raised when a constructor
      identifier [dc] of type [t] is defined multiple times, perhaps in
      different types. *)
  | DuplicateDataConstructor
    (* current definition *) (* previous definition *)
    of Location.t * Ast.dname * Ast.tname * Location.t

  (** [UnboundRecordField] is raised when a field label is
      used although it has not been defined. *)
  | UnboundRecordField of Location.t * Ast.lname

  (** [UnboundRecord] is raised when a record is used although it has
      not been defined. *)
  | UnboundRecord of Location.t * Ast.tname

  (** [DuplicateRecordField] is raised when a field label is
      defined multiple times, perhaps in different types. *)
  | DuplicateRecordField
            (* current definition *) (* previous definition *)
          of Location.t * Ast.lname * Ast.tname * Location.t

  (** [RepeatedRecordField] is raised when a field label is
      repeated in a record. *)
  | RepeatedRecordField of Ast.ident

  (** [IncompleteRecord adt f] is raised when a field label [f] is not
      initialized in a record [adt]. *)
  | IncompleteRecord of Ast.ident * string

  (** [InvalidRecordField f t] is raised when a field label [f] is used
      for a record type [t] that does not declare it. *)
  | InvalidRecordField of Ast.ident * Ast.ident

  (** [InvalidDataConstructorDefinition] is raised when the declared
      type scheme of a data constructor is not regular. *)
  | InvalidDataConstructorDefinition of Ast.ident

  (** [InvalidFieldDestructorDefinition] is raised when a field destructor
      scheme is not legal. *)
  | InvalidFieldDestructorDefinition of Ast.ident

  (** [UnboundTypeVariable] is raised when a variable identifier is
      used although it has not been defined. *)
  | UnboundTypeVariable of Location.t * Ast.tname

  (** [NonLinearPattern] is raised when at least two occurrences of a variable
      appear in a pattern. *)
  | NonLinearPattern of Location.t * string

  (** [InvalidPatternArgs c exp fnd] is raised when the arity [exp] of
      data constructor [c] is not respected in a pattern of arity [fnd]. *)
  | InvalidPatternArgs of Location.t * Ast.ident * int * int

  (** [UnboundConstructor] is raised when a type constructor is unbound. *)
  | UnboundTypeConstructor of Location.t * Ast.tname

  (** [KindError] is raised when the kind of types are not correct. *)
  | KindError of Location.t

  (** [PartialDataConstructorApplication c d u] is raised when the
      arity [d] of a data constructor [c] does not match the provided
      number [u] of arguments. *)
  | PartialDataConstructorApplication of Ast.ident * int * int

  (** [RepeatedFunctionParameter id idrep] is raised when a parameter
      with the same name [id] is repeated in a function definition. *)
  | RepeatedFunctionParameter of Ast.ident * Ast.ident

exception Error of typing_error

let msg m loc =
  Printf.sprintf m (Location.str_of_file_loc loc)

let error_msg = function
  | UnboundTypeIdentifier (p, TName t) ->
      msg "%s:\n Unbound type identifier `%s'.\n" p t

  | DuplicateTypeVariable t ->
      msg "%s:\n Duplicate type variable `%s'.\n"
        (Location.loc t) (Location.value t)

  | UnusedTypeVariable t ->
      msg "%s:\n Unused type variable `%s'.\n"
        (Location.loc t) (Location.value t)

  | InvalidTypeVariableIdentifier (p, TName v) ->
      msg "%s:\n `%s' type constructor is used as a type variable.\n"
        p v

  | UnboundDataConstructor (p, DName t) ->
      msg "%s:\n Unbound data constructor `%s'.\n" p t

  | DuplicateDataConstructor (ldc, DName dc, TName adt, ladt) ->
      msg
        "%s: Data constructor %s has already been defined by ADT %s at %s.\n"
        ldc dc adt (Location.str_of_file_loc ladt)

  | UnboundRecordField (p, LName t) ->
      msg "%s:\n Unbound record field `%s'.\n" p t

  | UnboundRecord (p, TName t) ->
      msg "%s:\n Unbound record `%s'.\n" p t

  | DuplicateRecordField (lr, LName f, TName adt, ladt) ->
      msg
        "%s: Record field %s has already been defined by ADT %s at %s.\n"
        lr f adt (Location.str_of_file_loc ladt)

  | RepeatedRecordField l ->
      msg "%s: Record field %s is repeated.\n"
        (Location.loc l) (Location.value l)

  | IncompleteRecord (t, l) ->
      msg "%s: Field %s of %s is not initialized.\n"
        (Location.loc t) l (Location.value t)

  | InvalidRecordField (l, t) ->
      msg "%s: Field %s of %s is not declated.\n"
        (Location.loc l) (Location.value l) (Location.value t)

  | InvalidDataConstructorDefinition k ->
      msg "%s:\n The type of the data constructor '%s' is incorrect.\n"
        (Location.loc k) (Location.value k)

  | InvalidFieldDestructorDefinition f ->
      msg "%s:\n The type of the field destructor `%s' is incorrect.\n"
        (Location.loc f) (Location.value f)

  | UnboundTypeVariable (p, TName t) ->
      msg "%s:\n Unbound type variable `%s'.\n" p t

  | NonLinearPattern (p, x) ->
      msg "%s:\n The variable '%s' occurs several times.\n" p x

  | InvalidPatternArgs (p, c, e, f) ->
      msg "%s:\n %d pattern arguments used for constructor %s expecting %d.\n"
        p f (Location.value c) e

  | UnboundTypeConstructor (p, TName t) ->
      msg "%s:\n Unbound type constructor `%s'.\n" p t

  | KindError p ->
      msg "%s:\n  Kind error.\n" p

  | PartialDataConstructorApplication (dc, d, u) ->
      msg
        "%s:\n The constructor %s needs %d argument%s not %d.\n"
        (Location.loc dc) (Location.value dc) d
        (if d > 1 then "s" else "")
        u

  | RepeatedFunctionParameter (p, p') ->
      msg "%s: parameter %s is repeated at %s."
        (Location.loc p) (Location.value p)
        (Location.str_of_file_loc (Location.loc p'))
