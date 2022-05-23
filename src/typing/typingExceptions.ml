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
  (* [UnboundTypeIdentifier t] is raised when an unbound type identifier
     `t` is found. *)
  | UnboundTypeIdentifier of Ast.full_tname

  (* [DuplicateTypeVariable v] is raised when a type variable declaration
     `v` is repeated in a type definition. *)
  | DuplicateTypeVariable of Ast.ident

  (* [UnusedTypeVariable v] is raised when a type variable declaration
     `v` is not used in a type definition. *)
  | UnusedTypeVariable of Ast.ident

  (* [InvalidTypeVariableIdentifier t] is raised when a type variable
     `t` is overwriting a type constructor. *)
  | InvalidTypeVariableIdentifier of Ast.full_tname

  (* [DuplicateTypeDefinition t] is raised when a type [t] is defined
     multiple times. *)
  | DuplicateTypeDefinition of Ast.full_tname

  (* [UnboundDataConstructor c] is raised when a constructor
     identifier `c` is used although it has not been defined. *)
  | UnboundDataConstructor of Ast.full_dname

  (* [DuplicateDataConstructor dc t] is raised when a constructor
     identifier [dc] of type [t] is defined multiple times, perhaps in
     different types. *)
  | DuplicateDataConstructor
    (* current definition *) (* previous definition *)
    of Ast.full_dname * Ast.full_tname * Location.t

  (* [UnboundRecordField l] is raised when a field label `l` is
     used although it has not been defined. *)
  | UnboundRecordField of Ast.full_lname

  (* [UnboundRecord r] is raised when a record `r` is used although it has
     not been defined. *)
  | UnboundRecord of Ast.full_tname

  (* [DuplicateRecordField l] is raised when a field label `l` is
     defined multiple times, perhaps in different types. *)
  | DuplicateRecordField
    (* current definition *) (* previous definition *)
    of Ast.full_lname * Ast.full_tname * Location.t

  (* [RepeatedRecordField l] is raised when a field label `l` is
     repeated in a record. *)
  | RepeatedRecordField of Ast.ident

  (* [InconsistentFieldModules] is raised when two fields of a record
     are module-qualified to belong to different modules. *)
  | InconsistentFieldModules of Ast.full_lname * Ast.full_lname

  (* [InconsistentRecordModule t f] is raised the module for a record type
     `t` and a field `f` for that type specify modules that don't
     match. *)
  | InconsistentRecordModule of Ast.full_tname * Ast.full_lname

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
  | UnboundTypeVariable of Ast.full_tname

  (* [PartialTypeConstructorApplication t d u] is raised when the
     arity [d] of a type constructor [t] does not match the provided
     number [u] of arguments. *)
  | PartialTypeConstructorApplication of Ast.full_tname * int * int

  (* [NonLinearPattern] is raised when at least two occurrences of a variable
     appear in a pattern. *)
  | NonLinearPattern of string

  (* [InvalidPatternArgs c exp fnd] is raised when the arity [exp] of
     data constructor [c] is not respected in a pattern of arity [fnd]. *)
  | InvalidPatternArgs of Ast.ident * int * int

  (* [UnboundConstructor] is raised when a type constructor is unbound. *)
  | UnboundTypeConstructor of Ast.full_tname

  (* [KindError] is raised when the kind of types are not correct. *)
  | KindError

  (* [PartialDataConstructorApplication c d u] is raised when the
     arity [d] of a data constructor [c] does not match the provided
     number [u] of arguments. *)
  | PartialDataConstructorApplication of Ast.ident * int * int

  (* [DuplicateFunctionDefinition id loc] is raised when a function
     [id] is redefined with a previous definition at [loc]. *)
  | DuplicateFunctionDefinition of string * Location.t

  (* [RepeatedFunctionParameter id idrep] is raised when a parameter
     with the same name [id] is repeated in a function definition. *)
  | RepeatedFunctionParameter of Ast.ident * Ast.ident

  (* [DuplicateModItem vid] is raised when a module [mid]
     contains multiple definitions of a value named [vid]. **)
  | DuplicateModItem of Ast.full_vname * Location.t

  (* [UnknownModule mid] is raised when a module name [mid] is
     referenced but not defined *)
  | UnknownModule of Ast.mname

  (* [UnknownModItem vid] is raised when a module-qualified value [vid] is
     referenced but not defined *)
  | UnknownModItem of Ast.full_vname

  (* [UnknownNonTerminal id] is raised when a non-terminal with name
     [id] has not been defined *)
  | UnknownNonTerminal of Ast.ident

  (* [DuplicateNonTerminal id] is raised when a non-terminal with name
     [id] has already been defined *)
  | DuplicateNonTerminal of Ast.full_nname * Location.t

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
  | NTEmptyRule of Ast.ident

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

  (* [NTIllegalMapAttributeAssignment nt id] is raised when a 'vector'
     assignment is used for inherited attribute [id] for non-terminal
     [nt] when not directly under a 'map_views' construct *)
  | NTIllegalMapAttributeAssignment of Ast.ident * Ast.ident

  (* Type abbreviations are currently not supported in (potentially) mutually
     recursive type declarations. *)
  | PotentiallyRecursiveTypeAbbreviation of Ast.ident

  (* [UnmatchedPattern pos p] is raised when a pattern match is not
     exhaustive and provides an example pattern p which is not covered
     by the match. *)
  (*Note: p is given as a string to avoid a dependency cycle *)
  | UnmatchedPattern of string

  (* [UselessPattern pos] is raised when a pattern match is
     redundant. *)
  | UselessPattern

  (* [UnboundIdentifier] is raised when an identifier is undefined in
     a particular context. *)
  | UnboundIdentifier of string

  (* [ZeroWidthBitVector] is raised when a bitvector<0> is specified. *)
  | ZeroWidthBitvector

  (* [InvalidBitrangeLowBound i] is raised when the lower bound of
     a bitrange is invalid (i.e. it is negative) *)
  | InvalidBitrangeLowBound of int

  (* [InvalidEmptyBitrange n m ] is raised when the selected range of
     bits is empty *)
  | InvalidEmptyBitrange of int * int

  (* [InvalidBitrangeOrder n m] is raised when the endpoints of the
     range are not specified in decreasing order. *)
  | InvalidBitrangeOrder of int * int

  (* [IncompleteBitfieldRanges bf n] is raised when the ranges of a
     bitfield [bf] do not cover index [n]. *)
  | IncompleteBitfieldRanges of Ast.ident * int

  (* [OverlappingBitfieldRanges bf f f' idx] is raised when the
     ranges of fields [f] and [f'] overlap at index [idx] *)
  | OverlappingBitfieldRanges of Ast.ident * Ast.ident * Ast.ident * int

  (* [InvalidRecordOperator op ] is raised when an unknown record
     operator [op] is specified. *)
  | InvalidRecordOperator of string

  (* [NotRecordType t] is raised when an record operator is applied on a
     non-record type [t]. *)
  | NotRecordType of Ast.ident

  (* [NotBitfieldType t] is raised when an bitfield operator is applied
     on a non-bitfield type [t]. *)
  | NotBitfieldType of Ast.ident

  (* [NotByteAligned ofs align pos] is raised when a rule element is not
     aligned to [align] bits at [pos] and is off by [ofs] bits. *)
  | NotByteAligned of int * int * rule_pos

  (* [InvalidAlignment a] is raised when an alignment value that is
     not a multiple of 8 is specified *)
  | InvalidAlignment of Ast.bitint

  (* [ZeroWidthAlignment] is raised when an alignment spec or padding
     is not necessary since it matches 0 bits *)
  | ZeroWidthAlignment

  (* [Non_constant_numerical_arg m i] is raised when a non-numerical
     argument is given to a standard library api 'm.i' that expects a
     numerical argument. *)
  | Non_constant_numerical_arg of Ast.ident * Ast.ident

  (* [Possible_division_by_zero] is raised during constant folding *)
  | Possible_division_by_zero

  (* [Non_literal_string_arg s] is raised when a non-literal argument
     is given to a standard library api 'm.i' that expects a literal
     string argument. *)
  | Non_literal_string_arg of Ast.ident * Ast.ident

  (* [Not_character_class] is raised when a character class is
     not provided as a regular expression (e.g. as the left operand
     of a difference operator). *)
  | Not_character_class

  (* [Unknown_character_class] is raised when an unknown character class is
     specified. *)
  | Unknown_character_class of Ast.ident

  (* [Not_literal_set] is raised when a set of literals is expected
     (e.g. as the right operand of a difference operator). *)
  | Not_literal_set

  (* [Not_in_character_set id l] is raised when a literal [l] is not
     a member of character class [id]. *)
  | Not_in_character_set of Ast.ident * Ast.literal

  (* [Inconsistent_range_literals s e sl el] is raised when the starting [s]
     and ending literals [e] in a literal range have unequal lengths
     [sl] and [el] respectively. *)
  | Inconsistent_range_literals of Ast.literal * Ast.literal * int * int

  (* [Inconsistent_literal_ranges s e idx] is raised when the starting [s]
     and ending literal [e] in a literal range are inconsistent at
     index [idx]. *)
  | Inconsistent_literal_range of Ast.literal * Ast.literal * int

  (* [Not_a_character] is raised when a literal does not decode to a
     valid character. *)
  | Not_a_character of Ast.literal

  (* [RepeatedDecorator d] is raised when multiple uses of a
     decorator type [d] appear in a decorator specification of a
     non-terminal. *)
  | RepeatedDecoratorType of Ast.ident

  (* [RepeatedDecoratorKey d k] is raised when multiple uses of an
     decorator key [k] appear in a decorator type [d]. *)
  | RepeatedDecoratorKey of Ast.ident * Ast.ident

  (* [InvalidDecoratorName d] is raised when name of decorator
     [d] is invalid as a non-terminal name. *)
  | InvalidDecoratorName of Ast.ident

  (* [UnvaluedDecoratorKey d k] is raised when a key [k] of an
     decorator [d] does not specify a value. *)
  | UnvaluedDecoratorKey of Ast.ident * Ast.ident

  (* [InvalidDecoratorKeyValue d k v] is raised when an
     invalid value [v] is specified for a key [k] of a
     decorator [d]. *)
  | InvalidDecoratorKeyValue of Ast.ident * Ast.ident * Ast.ident

  (* [IllegalBinding b] is raised when a special value cannot be
     bound to a variable.  The value is typically related to
     standard-library support for higher-order functions. *)
  | IllegalBinding of Ast.modident * Ast.ident

  (* [IllegalFunctionArgument (m, f)] is raised when the argument
     in function position for a call to the higher-order standard
     library function [m.f] is not a symbol.
   *)
  | IllegalFunctionArgument of Ast.modident * Ast.ident

  (* [FunctionCallArity f d u] is raised when the number of arguments
     [d] defined for function [f] does not match the provided
     number [u] of arguments. *)
  | FunctionCallArity of string * int * int

  (* [IncompatibleArityFunctionArgument [ho hoa f fa ] is raised when
   * the arity [fa] of function [f] is incompatible with arity [hoa]
   * expected by higher-order construct [ho]. *)
  | IncompatibleArityFunctionArgument of string * int * string * int

exception Error of Location.t * typing_error

let str_of_rule_pos = function
  | At_begin -> "beginning"
  | At_end   -> "end"

let error_msg = function
  | UnboundTypeIdentifier (m, (TName t)) ->
      Printf.sprintf "Unbound type identifier `%s%s'."
        (AstUtils.mk_modprefix m) t

  | DuplicateTypeVariable t ->
      Printf.sprintf "Duplicate type variable `%s'." (Location.value t)

  | UnusedTypeVariable t ->
      Printf.sprintf "Unused type variable `%s'." (Location.value t)

  | InvalidTypeVariableIdentifier (m, (TName v)) ->
      Printf.sprintf
        "`%s%s' type constructor is used as a type variable."
        (AstUtils.mk_modprefix m) v
  | DuplicateTypeDefinition (m, TName t) ->
      Printf.sprintf "Type '%s%s' has already been defined."
        (AstUtils.mk_modprefix m) t

  | PartialTypeConstructorApplication ((m, TName t), d, u) ->
      Printf.sprintf
        "Type constructor `%s%s' needs %d argument%s but %d are provided."
        (AstUtils.mk_modprefix m) t d
        (if d > 1 then "s" else "")
        u

  | UnboundDataConstructor (m, (DName t)) ->
      Printf.sprintf "Unbound data constructor `%s%s'."
        (AstUtils.mk_modprefix m) t

  | DuplicateDataConstructor ((m, DName dc), (m', TName adt), ladt) ->
      Printf.sprintf
        "Data constructor `%s%s' has already been defined by ADT `%s%s' at %s."
        (AstUtils.mk_modprefix m) dc (AstUtils.mk_modprefix m') adt
        (Location.str_of_file_loc ladt)

  | UnboundRecordField (m, (LName t)) ->
      Printf.sprintf "Unbound record field `%s%s'."
        (AstUtils.mk_modprefix m) t

  | UnboundRecord (m, (TName t)) ->
      Printf.sprintf "Unbound record `%s%s'."
        (AstUtils.mk_modprefix m) t

  | DuplicateRecordField ((m, LName f), (m', TName adt), ladt) ->
      Printf.sprintf
        "Record field `%s%s' has already been defined by ADT `%s%s' at %s."
        (AstUtils.mk_modprefix m) f (AstUtils.mk_modprefix m') adt
        (Location.str_of_file_loc ladt)

  | RepeatedRecordField l ->
      Printf.sprintf "Record field `%s' is repeated."
        (Location.value l)

  | InconsistentFieldModules ((m, LName l), (m', LName l')) ->
      Printf.sprintf
        "Fields `%s%s' and `%s%s' do not belong to the same module."
        (AstUtils.mk_modprefix m) l (AstUtils.mk_modprefix m') l'

  | InconsistentRecordModule ((m, TName t), (m', LName l)) ->
      Printf.sprintf
        "Modules for record type `%s%s' and field `%s%s' do not match."
        (AstUtils.mk_modprefix m) t (AstUtils.mk_modprefix m') l

  | IncompleteRecord (t, l) ->
      Printf.sprintf "Field `%s' of `%s' is not initialized."
        l (Location.value t)

  | InvalidRecordField (l, t) ->
      Printf.sprintf "Field `%s' of `%s' is not declared."
        (Location.value l) (Location.value t)

  | InvalidDataConstructorDefinition k ->
      Printf.sprintf "The type of the data constructor '%s' is incorrect."
        (Location.value k)

  | InvalidFieldDestructorDefinition f ->
      Printf.sprintf "The type of the field destructor `%s' is incorrect."
        (Location.value f)

  | UnboundTypeVariable (m, (TName t)) ->
      Printf.sprintf "Unbound type variable `%s%s'."
        (AstUtils.mk_modprefix m) t

  | NonLinearPattern x ->
      Printf.sprintf "The pattern variable '%s' cannot appear more than once." x

  | InvalidPatternArgs (c, e, f) ->
      Printf.sprintf "%d pattern arguments used for constructor `%s', expecting %d."
        f (Location.value c) e

  | UnboundTypeConstructor (m, (TName t)) ->
      Printf.sprintf "Unbound type constructor `%s%s'."
        (AstUtils.mk_modprefix m) t

  | KindError ->
      "Kind error."

  | PartialDataConstructorApplication (dc, d, u) ->
      Printf.sprintf
        "The constructor `%s' needs %d argument%s not %d."
        (Location.value dc) d
        (if d > 1 then "s" else "")
        u

  | DuplicateFunctionDefinition (f, p') ->
      Printf.sprintf "Redefinition of function `%s' at %s."
        f (Location.str_of_file_loc p')

  | RepeatedFunctionParameter (p, p') ->
      Printf.sprintf "Parameter `%s' is repeated at %s."
        (Location.value p) (Location.str_of_file_loc (Location.loc p'))

  | DuplicateModItem ((m, VName v), loc) ->
      Printf.sprintf "Redefinition of value `%s' of module `%s' defined at %s."
        v (AstUtils.str_of_mod m) (Location.str_of_file_loc loc)

  | UnknownModule mid ->
      Printf.sprintf "Unknown module `%s'." (AstUtils.str_of_mod mid)

  | UnknownModItem (m, VName vid) ->
      Printf.sprintf "Undefined value `%s' of module `%s'."
        vid (AstUtils.str_of_mod m)

  | UnknownNonTerminal nid ->
      Printf.sprintf "Non-terminal `%s' is not declared."
        (Location.value nid)

  | DuplicateNonTerminal ((m, NName s), p') ->
      Printf.sprintf "Non-terminal `%s%s' was already defined at `%s'."
        (AstUtils.mk_modprefix m) s (Location.str_of_file_loc p')

  | NTAttributesNotRecordType (ntid, t) ->
      Printf.sprintf "Type `%s' for the attributes of `%s' is not a record type."
        (Location.value t) (Location.value ntid)

  | NTTypeNotInferrable ntid ->
      Printf.sprintf
        "Non-terminal `%s' has an undeclared type that cannot be inferred."
        (Location.value ntid)

  | NTNoRules ntid ->
      Printf.sprintf "Non-terminal `%s' has no valid production rules."
        (Location.value ntid)

  | NTEmptyRule ntid ->
      Printf.sprintf
        "Invalid empty production rule for non-terminal `%s'."
        (Location.value ntid)

  | NTRepeatedBinding (ntid, id, id') ->
      Printf.sprintf
        "Binding `%s' of non-terminal `%s' collides with the binding at %s."
        (Location.value id) (Location.value ntid)
        (Location.str_of_file_loc (Location.loc id'))

  | NTInheritedUnspecified (ntid, id) ->
      Printf.sprintf
        "Inherited attribute `%s' of non-terminal `%s' is unspecified."
        id (Location.value ntid)

  | NTUnknownInheritedAttribute (ntid, id) ->
      Printf.sprintf
        "Non-terminal `%s' does not define inherited attribute `%s'."
        (Location.value ntid) (Location.value id)

  | NTIllegalMapAttributeAssignment (ntid, id) ->
      Printf.sprintf
        "A map-assignment is being used for inherited attribute `%s' when non-terminal `%s' is not directly in the scope of a map-views."
        (Location.value ntid) (Location.value id)

  | PotentiallyRecursiveTypeAbbreviation id ->
      Printf.sprintf
        "Type abbreviations (e.g. `%s') are not supported in type definition sets."
        (Location.value id)

  | UnmatchedPattern p ->
      Printf.sprintf
        "Pattern matching is not exhaustive: an example of unmatched value: %s."
        p

  | UselessPattern ->
      "This pattern is redundant, and may indicate an error."

  | UnboundIdentifier t ->
      Printf.sprintf "Unbound identifier `%s'." t

  | ZeroWidthBitvector ->
      "A zero-width bitvector is not a valid type."

  | InvalidBitrangeLowBound b ->
      Printf.sprintf "%d is an invalid low bound for bitvector range." b

  | InvalidEmptyBitrange (n, m) ->
      Printf.sprintf "%d-%d is an invalid (empty) range." n m

  | InvalidBitrangeOrder (n, m) ->
      Printf.sprintf "Index range %d-%d is in an invalid order." n m

  | IncompleteBitfieldRanges (bf, idx) ->
      Printf.sprintf
        "Specified ranges of bitfield `%s' do not cover index %d."
        (Location.value bf) idx

  | OverlappingBitfieldRanges (bf, f, f', idx) ->
      Printf.sprintf
        "Fields `%s' and `%s' of bitfield `%s' overlap at index %d."
        (Location.value f) (Location.value f') (Location.value bf) idx

  | InvalidRecordOperator op ->
      Printf.sprintf "Invalid record operator `%s'." op

  | NotRecordType t ->
      Printf.sprintf "`%s' is not a record type." (Location.value t)

  | NotBitfieldType t ->
      Printf.sprintf "`%s' is not a bitfield type." (Location.value t)

  | NotByteAligned (ofs, align, pos) ->
      Printf.sprintf
        "The %s of this rule element is not aligned to %d bits (off by %d bits)."
        (str_of_rule_pos pos) align ofs
  | InvalidAlignment a ->
      Printf.sprintf "Alignment %d is not byte-aligned." (Location.value a)
  | ZeroWidthAlignment ->
      "Unnecessary alignment (matches 0 bits)."
  | Non_constant_numerical_arg (m, i) ->
      Printf.sprintf
        "Operation `%s.%s' requires this to be a constant numerical argument."
        (Location.value m) (Location.value i)

  | Possible_division_by_zero ->
      "Possible division by zero."

  | Non_literal_string_arg (m, i) ->
      Printf.sprintf
        "Operation `%s.%s' requires this to be a literal string argument."
        (Location.value m) (Location.value i)

  | Not_character_class ->
      "A character class was expected."
  | Unknown_character_class id ->
      Printf.sprintf "Unknown character class `%s'." (Location.value id)
  | Not_literal_set ->
      "A literal set was expected."
  | Not_in_character_set (id, l) ->
      Printf.sprintf "Literal `%s' is not in character class `%s'."
        (Location.value l) (Location.value id)
  | Inconsistent_range_literals (s, e, sl, el) ->
      let ss, se = Location.value s, Location.value e in
      Printf.sprintf
        "Starting (`%s') and ending (`%s') literals in range have inconsistent lengths %d and %d."
        ss se sl el
  | Inconsistent_literal_range (s, e, idx) ->
      Printf.sprintf
        "Starting literal `%s' at position %d of range is not smaller than ending literal `%s'."
        (Location.value s) idx (Location.value e)

  | Not_a_character l ->
      Printf.sprintf "Not a valid character `%s'." (Location.value l)

  | RepeatedDecoratorType a ->
      Printf.sprintf "Decorator `%s' cannot be repeated."
        (Location.value a)

  | InvalidDecoratorName a ->
      Printf.sprintf "Decorator `%s' is invalid as a non-terminal name."
        (Location.value a)

  | RepeatedDecoratorKey (a, k) ->
      Printf.sprintf "Key `%s' of decorator `%s' cannot be repeated."
        (Location.value k) (Location.value a)

  | UnvaluedDecoratorKey (a, k) ->
      Printf.sprintf "Key `%s' of decorator `%s' does not have a value."
        (Location.value k) (Location.value a)

  | InvalidDecoratorKeyValue (a, k, v) ->
      Printf.sprintf "Key `%s' of decorator `%s' has non-boolean value `%s'."
        (Location.value k) (Location.value a) (Location.value v)

  | IllegalBinding (m, i) ->
      Printf.sprintf "`%s.%s' cannot be bound to a variable."
        (Location.value m) (Location.value i)

  | IllegalFunctionArgument (m, f) ->
      Printf.sprintf "The function argument in the call to `%s.%s' is illegal."
        (Location.value m) (Location.value f)

  | FunctionCallArity (f, d, u) ->
      Printf.sprintf "Function `%s' expects %d arguments but %d are provided."
        f d u

  | IncompatibleArityFunctionArgument (ho, hoa, f, fa) ->
      Printf.sprintf
        "The function `%s' takes %d arguments, but %s expects a function argument that takes %d args."
        f fa ho hoa
