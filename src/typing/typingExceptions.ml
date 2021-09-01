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

open Parsing

type rule_pos =
  | At_begin
  | At_end

type typing_error =
  (* [UnboundTypeIdentifier] is raised when an unbound type identifier
     is found. *)
  | UnboundTypeIdentifier of Location.t * Ast.tname

  (* [DuplicateTypeVariable] is raised when a type variable declaration
     is repeated in a type definition. *)
  | DuplicateTypeVariable of Ast.ident

  (* [UnusedTypeVariable] is raised when a type variable declaration
     is not used in a type definition. *)
  | UnusedTypeVariable of Ast.ident

  (* [InvalidTypeVariableIdentifier] is raised when a type variable is
     overwriting a type constructor. *)
  | InvalidTypeVariableIdentifier of Location.t * Ast.tname

  (* [DuplicateTypeDefinition t] is raised when a type [t] is defined
     multiple times. *)
  | DuplicateTypeDefinition of Location.t * Ast.tname

  (* [UnboundDataConstructor] is raised when a constructor identifier is
     used although it has not been defined. *)
  | UnboundDataConstructor of Location.t * Ast.dname

  (* [DuplicateDataConstructor dc t] is raised when a constructor
     identifier [dc] of type [t] is defined multiple times, perhaps in
     different types. *)
  | DuplicateDataConstructor
    (* current definition *) (* previous definition *)
    of Location.t * Ast.dname * Ast.tname * Location.t

  (* [UnboundRecordField] is raised when a field label is
     used although it has not been defined. *)
  | UnboundRecordField of Location.t * Ast.lname

  (* [UnboundRecord] is raised when a record is used although it has
     not been defined. *)
  | UnboundRecord of Location.t * Ast.tname

  (* [DuplicateRecordField] is raised when a field label is
     defined multiple times, perhaps in different types. *)
  | DuplicateRecordField
            (* current definition *) (* previous definition *)
          of Location.t * Ast.lname * Ast.tname * Location.t

  (* [RepeatedRecordField] is raised when a field label is
     repeated in a record. *)
  | RepeatedRecordField of Ast.ident

  (* [IncompleteRecord adt f] is raised when a field label [f] is not
     initialized in a record [adt]. *)
  | IncompleteRecord of Ast.ident * string

  (* [InvalidRecordField f t] is raised when a field label [f] is used
     for a record type [t] that does not declare it. *)
  | InvalidRecordField of Ast.ident * Ast.ident

  (* [InvalidDataConstructorDefinition] is raised when the declared
     type scheme of a data constructor is not regular. *)
  | InvalidDataConstructorDefinition of Ast.ident

  (* [InvalidFieldDestructorDefinition] is raised when a field destructor
     scheme is not legal. *)
  | InvalidFieldDestructorDefinition of Ast.ident

  (* [UnboundTypeVariable] is raised when a variable identifier is
     used although it has not been defined. *)
  | UnboundTypeVariable of Location.t * Ast.tname

  (* [PartialTypeConstructorApplication t d u] is raised when the
     arity [d] of a type constructor [t] does not match the provided
     number [u] of arguments. *)
  | PartialTypeConstructorApplication of Location.t * Ast.tname * int * int

  (* [NonLinearPattern] is raised when at least two occurrences of a variable
     appear in a pattern. *)
  | NonLinearPattern of Location.t * string

  (* [InvalidPatternArgs c exp fnd] is raised when the arity [exp] of
     data constructor [c] is not respected in a pattern of arity [fnd]. *)
  | InvalidPatternArgs of Location.t * Ast.ident * int * int

  (* [UnboundConstructor] is raised when a type constructor is unbound. *)
  | UnboundTypeConstructor of Location.t * Ast.tname

  (* [KindError] is raised when the kind of types are not correct. *)
  | KindError of Location.t

  (* [PartialDataConstructorApplication c d u] is raised when the
     arity [d] of a data constructor [c] does not match the provided
     number [u] of arguments. *)
  | PartialDataConstructorApplication of Ast.ident * int * int

  (* [RepeatedFunctionParameter id idrep] is raised when a parameter
     with the same name [id] is repeated in a function definition. *)
  | RepeatedFunctionParameter of Ast.ident * Ast.ident

  (* [DuplicateModItem mid vid] is raised when a module [mid]
     contains multiple definitions of a value named [vid]. **)
  | DuplicateModItem of Location.t * Ast.mname * Ast.dname * Location.t

  (* [UnknownModule mid] is raised when a module name [mid] is
     referenced but not defined *)
  | UnknownModule of Location.t * Ast.mname

  (* [UnknownModItem mid vid] is raised when a value [vid] of module [mid] is
     referenced but not defined *)
  | UnknownModItem of Location.t * Ast.mname * Ast.dname

  (* [UnknownNonTerminal id] is raised when a non-terminal with name
     [id] has not been defined *)
  | UnknownNonTerminal of Ast.ident

  (* [DuplicateNonTerminal id] is raised when a non-terminal with name
     [id] has already been defined *)
  | DuplicateNonTerminal of Location.t * Ast.nname * Location.t

  (* [NTAttrsNotRecordType ntid t] is raised when the type [t] given
     for the attributes of the non-terminal [ntid] is not a record
     type. *)
  | NTAttributesNotRecordType of Ast.ident * Ast.ident

  (* [NTTypeNotInferrable ntid] is raised when no type is declared
     for the synthesized attributes of the non-terminal [ntid], and
     it cannot be inferred from the productions of [ntid]. *)
  | NTTypeNotInferrable of Ast.ident

  (* [NTNoRules ntid] is raised when no production rules have been
     specified for the non-terminal [ntid]. *)
  | NTNoRules of Ast.ident

  (* [NTEmptyRule ntid] is raised when an empty production rule has been
     specified for the non-terminal [ntid]. *)
  | NTEmptyRule of Ast.ident * Location.t

  (* [NTRepeatedBinding nt id id'] is raised when a rule for
     non-terminal [nt] has a binding [id] with the same name as
     an earlier binding [id']. *)
  | NTRepeatedBinding of Ast.ident * Ast.ident * Ast.ident

  (* [NTInheritedUnspecified nt id] is raised when a rule calls a
     non-terminal but does not specify a value for its inherited
     attribute [id] *)
  | NTInheritedUnspecified of Ast.ident * string

  (* [NTUnknownInheritedAttribute nt id] is raised when an attribute [id] is
     not defined to be part of the definition of non-terminal [nt] *)
  | NTUnknownInheritedAttribute of Ast.ident * Ast.ident

  (* Type abbreviations are currently not supported in (potentially) mutually
     recursive type declarations. *)
  | PotentiallyRecursiveTypeAbbreviation of Ast.ident

  (* [UnmatchedPattern pos p] is raised when a pattern match is not
     exhaustive and provides an example pattern p which is not covered
     by the match. *)
  (*Note: p is given as a string to avoid a dependency cycle *)
  | UnmatchedPattern of Location.t * string

  (* [UnboundIdentifier] is raised when an identifier is undefined in
     a particular context. *)
  | UnboundIdentifier of Location.t * string

  (* [ZeroWidthBitVector] is raised when a bitvector<0> is specified. *)
  | ZeroWidthBitvector of Location.t

  (* [InvalidBitrangeLowBound i] is raised when the lower bound of
     a bitrange is invalid (i.e. it is negative) *)
  | InvalidBitrangeLowBound of Location.t * int

  (* [InvalidEmptyBitrange n m ] is raised when the selected range of
     bits is empty *)
  | InvalidEmptyBitrange of Location.t * int * int

  (* [InvalidBitrangeOrder n m] is raised when the endpoints of the
     range are not specified in decreasing order. *)
  | InvalidBitrangeOrder of Location.t * int * int

  (* [IncompleteBitfieldRanges bf n] is raised when the ranges of a
     bitfield [bf] do not cover index [n]. *)
  | IncompleteBitfieldRanges of Ast.ident * int

  (* [OverlappingBitfieldRanges bf f f' idx] is raised when the
     ranges of fields [f] and [f'] overlap at index [idx] *)
  | OverlappingBitfieldRanges of Ast.ident * Ast.ident * Ast.ident * int

  (* [InvalidRecordOperator op ] is raised when an unknown record
     operator [op] is specified. *)
  | InvalidRecordOperator of Location.t * string

  (* [NotRecordType t] is raised when an record operator is applied on a
     non-record type [t]. *)
  | NotRecordType of Ast.ident

  (* [NotBitfieldType t] is raised when an bitfield operator is applied
     on a non-bitfield type [t]. *)
  | NotBitfieldType of Ast.ident

  (* [NotByteAligned ofs align pos] is raised when a rule element is not
     aligned to [align] bits at [pos] and is off by [ofs] bits. *)
  | NotByteAligned of Location.t * int * int * rule_pos

  (* [InvalidAlignment a] is raised when an alignment value that is
     not a multiple of 8 is specified *)
  | InvalidAlignment of Ast.bitint

  (* [ZeroWidthAlignment] is raised when an alignment spec or padding
     is not necessary since it matches 0 bits *)
  | ZeroWidthAlignment of Location.t

  (* [Non_constant_numerical_arg m i] is raised when a non-numerical
     argument is given to a standard library api 'm.i' that expects a
     numerical argument. *)
  | Non_constant_numerical_arg of Location.t * Ast.ident * Ast.ident

  (* [Possible_division_by_zero] is raised during constant folding *)
  | Possible_division_by_zero of Location.t

  (* [Non_literal_string_arg s] is raised when a non-literal argument
     is given to a standard library api 'm.i' that expects a literal
     string argument. *)
  | Non_literal_string_arg of Location.t * Ast.ident * Ast.ident

exception Error of typing_error

let str_of_rule_pos = function
  | At_begin -> "beginning"
  | At_end   -> "end"

let msg m loc =
  Printf.sprintf m (Location.str_of_loc loc)

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
  | DuplicateTypeDefinition (p, TName t) ->
      msg "%s:\n Type '%s' has already been defined.\n" p t

  | PartialTypeConstructorApplication (p, (TName t), d, u) ->
      msg
        "%s:\n Type constructor `%s' needs %d argument%s not %d.\n"
        p  t d
        (if d > 1 then "s" else "")
        u

  | UnboundDataConstructor (p, DName t) ->
      msg "%s:\n Unbound data constructor `%s'.\n" p t

  | DuplicateDataConstructor (ldc, DName dc, TName adt, ladt) ->
      msg
        "%s:\n Data constructor `%s' has already been defined by ADT `%s' at %s.\n"
        ldc dc adt (Location.str_of_file_loc ladt)

  | UnboundRecordField (p, LName t) ->
      msg "%s:\n Unbound record field `%s'.\n" p t

  | UnboundRecord (p, TName t) ->
      msg "%s:\n Unbound record `%s'.\n" p t

  | DuplicateRecordField (lr, LName f, TName adt, ladt) ->
      msg
        "%s:\n Record field `%s' has already been defined by ADT `%s' at %s.\n"
        lr f adt (Location.str_of_file_loc ladt)

  | RepeatedRecordField l ->
      msg "%s:\n Record field `%s' is repeated.\n"
        (Location.loc l) (Location.value l)

  | IncompleteRecord (t, l) ->
      msg "%s:\n Field `%s' of `%s' is not initialized.\n"
        (Location.loc t) l (Location.value t)

  | InvalidRecordField (l, t) ->
      msg "%s:\n Field `%s' of `%s' is not declared.\n"
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
      msg "%s:\n The pattern variable '%s' cannot appear more than once.\n" p x

  | InvalidPatternArgs (p, c, e, f) ->
      msg "%s:\n %d pattern arguments used for constructor `%s', expecting %d.\n"
        p f (Location.value c) e

  | UnboundTypeConstructor (p, TName t) ->
      msg "%s:\n Unbound type constructor `%s'.\n" p t

  | KindError p ->
      msg "%s:\n  Kind error.\n" p

  | PartialDataConstructorApplication (dc, d, u) ->
      msg
        "%s:\n The constructor `%s' needs %d argument%s not %d.\n"
        (Location.loc dc) (Location.value dc) d
        (if d > 1 then "s" else "")
        u

  | RepeatedFunctionParameter (p, p') ->
      msg "%s:\n parameter `%s' is repeated at %s.\n"
        (Location.loc p) (Location.value p)
        (Location.str_of_file_loc (Location.loc p'))

  | DuplicateModItem (p, MName m, DName v, loc) ->
      msg "%s:\n redefinition of value `%s' of module `%s' defined at %s.\n"
        p v m (Location.str_of_file_loc loc)

  | UnknownModule (p, MName mid) ->
      msg "%s:\n unknown module `%s'\n."
        p mid

  | UnknownModItem (p, MName mid, DName vid) ->
      msg "%s:\n undefined value `%s' of module `%s'.\n"
        p vid mid

  | UnknownNonTerminal nid ->
      msg "%s:\n Non-terminal `%s' is not declared.\n"
        (Location.loc nid) (Location.value nid)

  | DuplicateNonTerminal (p, NName s, p') ->
      msg "%s:\n Non-terminal `%s' was already defined at `%s'.\n"
        p s (Location.str_of_file_loc p')

  | NTAttributesNotRecordType (ntid, t) ->
      msg "%s:\n Type `%s' for the attributes of `%s' is not a record type.\n"
        (Location.loc t) (Location.value t) (Location.value ntid)

  | NTTypeNotInferrable ntid ->
      msg
        "%s:\n Non-terminal `%s' has an undeclared type that cannot be inferred.\n"
        (Location.loc ntid) (Location.value ntid)

  | NTNoRules ntid ->
      msg
        "%s\n Non-terminal `%s' has no valid production rules."
        (Location.loc ntid) (Location.value ntid)

  | NTEmptyRule (ntid, loc) ->
      msg
        "%s\n Invalid empty production rule for non-terminal `%s'."
        loc (Location.value ntid)

  | NTRepeatedBinding (ntid, id, id') ->
      msg
        "%s:\n Binding `%s' of non-terminal `%s' collides with the binding at %s.\n"
        (Location.loc id) (Location.value id) (Location.value ntid)
        (Location.str_of_file_loc (Location.loc id'))

  | NTInheritedUnspecified (ntid, id) ->
      msg
        "%s:\n Inherited attribute `%s' of non-terminal `%s' is unspecified.\n"
        (Location.loc ntid) (Location.value ntid) id

  | NTUnknownInheritedAttribute (ntid, id) ->
      msg
        "%s:\n Non-terminal `%s' does not define inherited attribute `%s'.\n"
        (Location.loc id) (Location.value ntid) (Location.value id)

  | PotentiallyRecursiveTypeAbbreviation id ->
      msg
        "%s:\n Type abbreviations (e.g. `%s') are not supported in type definition sets.\n"
        (Location.loc id) (Location.value id)

  | UnmatchedPattern (loc, p) ->
      msg
        "%s:\n Pattern matching is not exhaustive: an example of unmatched value: %s\n"
        loc p

  | UnboundIdentifier (p, t) ->
      msg "%s:\n Unbound identifier `%s'.\n" p t

  | ZeroWidthBitvector l ->
      msg "%s:\n a zero-width bitvector is not a valid type.\n" l

  | InvalidBitrangeLowBound (loc, b) ->
      msg "%s:\n %d is an invalid low bound for bitvector range.\n" loc b

  | InvalidEmptyBitrange (loc, n, m) ->
      msg "%s:\n %d-%d is an invalid (empty) range.\n" loc n m

  | InvalidBitrangeOrder (loc, n, m) ->
      msg "%s:\n index range %d-%d is in an invalid order.\n" loc n m

  | IncompleteBitfieldRanges (bf, idx) ->
      msg
        "%s:\n specified ranges of bitfield `%s' do not cover index %d.\n"
        (Location.loc bf) (Location.value bf) idx

  | OverlappingBitfieldRanges (bf, f, f', idx) ->
      msg
        "%s:\n fields `%s' and `%s' of bitfield `%s' overlap at index %d.\n"
        (Location.loc bf) (Location.value f) (Location.value f')
        (Location.value bf) idx

  | InvalidRecordOperator(loc, op) ->
      msg "%s:\n invalid record operator `%s'.\n" loc op

  | NotRecordType t ->
      msg "%s:\n `%s' is not a record type.\n"
        (Location.loc t) (Location.value t)

  | NotBitfieldType t ->
      msg "%s:\n `%s' is not a bitfield type.\n"
        (Location.loc t) (Location.value t)

  | NotByteAligned (loc, ofs, align, pos) ->
      msg
        "%s:\n the %s of this rule element is not aligned to %d bits (off by %d bits).\n"
        loc (str_of_rule_pos pos) align ofs
  | InvalidAlignment a ->
      msg "%s:\n alignment %d is not byte-aligned.\n"
        (Location.loc a) (Location.value a)
  | ZeroWidthAlignment l ->
      msg "%s:\n unnecessary alignment (matches 0 bits).\n" l
  | Non_constant_numerical_arg (loc, m, i) ->
      msg
        "%s:\n operation `%s.%s' requires this to be a constant numerical argument.\n"
        loc (Location.value m) (Location.value i)

  | Non_literal_string_arg (loc, m, i) ->
      msg
        "%s:\n operation `%s.%s' requires this to be a literal string argument.\n"
        loc (Location.value m) (Location.value i)

  | Possible_division_by_zero l ->
      msg "%s:\n possible division by zero.\n" l
