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

(** This module provides the type algebra for the Parsley language. *)

(** The type algebra augments the {!CoreAlgebra} to relate it with
    the Parsley source language. *)

open Parsing

(** A type constructor is a type variable with higher-order kind.
    It is introduced as any type variable in the multi-equation set
    during the constraint generation. Then, an environment is given to
    the algebra in order to retrieve the type variable associated
    to the string representation of the type constructor. *)
type 'a environment = Ast.full_tname -> 'a CoreAlgebra.arterm

(** Head symbols. *)
type symbol

(** Associativity of a symbol. *)
type associativity =
  | Assoc_left
  | Assoc_none
  | Assoc_right
  | Assoc_enclosed of string * string

(** Syntactic information for types *)
type syntax =
  (* infix *) bool * associativity * (* priority *) int

(** [as_symbol s] maps the string [s] to a symbol if [s] is a
    valid symbol name. *)
val as_symbol: Ast.full_tname -> symbol option

(** [associativity s] returns the associativity of [s]. *)
val associativity: symbol -> associativity

(** [priority s] returns the priority of [s]. *)
val priority: symbol -> int

(** [infix s] tests if [s] is infix. *)
val infix: symbol -> bool

(** Type representation *)

(** The type of predefined data constructors. *)
type builtin_dataconstructor =
  Ast.dname * Ast.tname list * Ast.type_expr

(** The type of predefined values. *)
type builtin_value =
  Ast.vname * Ast.tname list * Ast.type_expr

(** The representation of predefined types. *)
type builtin_type =
  Ast.tname * (Ast.kind * syntax * builtin_dataconstructor list)

(** The type information for a builtin module. *)
type builtin_module =
  {mod_name:   Ast.mod_qual;
   mod_values: builtin_value list}

(** The representation of predefined non-terminals, with their
 ** inherited attributes and their types. *)
type builtin_non_term =
  Ast.nname * (unit Ast.var * Ast.type_expr * unit) list * Ast.type_expr

(** Operators on the type representation *)

(** [option env t] returns the type [option t] *)
val option: 'a environment -> 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm

(** [list env t] returns the type [list t] *)
val list: 'a environment -> 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm

(** [tuple env ts] returns [t0 * ... * tn]. *)
val tuple: 'a environment -> 'a CoreAlgebra.arterm list -> 'a CoreAlgebra.arterm

(** [arrow env t1 t2] returns the type [t1 -> t2]. *)
val arrow: 'a environment -> 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm

(** [concrete_bitvector env n] returns the bitvector type for an integer width [n] *)
val concrete_bitvector: 'a environment -> int -> 'a CoreAlgebra.arterm

(** [abstract_bitvector env t] returns the bitvector type [bitvector t] *)
val abstract_bitvector: 'a environment -> 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm

(** [arrow env ts] returns the type [t0 -> ... -> tn]. *)
val n_arrows: 'a environment -> 'a CoreAlgebra.arterm list -> 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm

(** [result_type env t] returns the result type of the type [t] if
    [t] is an arrow type. *)
val result_type:  'a environment -> 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm

(** [arg_types env t] returns the argument types of the type [t] if
    [t] is an arrow type. *)
val arg_types: 'a environment -> 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm list

val tycon_args: 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm list
val tycon_name: 'a CoreAlgebra.arterm -> 'a CoreAlgebra.arterm

(** [type_of_primitive p] returns the type of a source language primitive. *)
val type_of_primitive: 'a environment -> Ast.primitive_literal -> 'a CoreAlgebra.arterm

(** [character_classes] is an array of the builtin character classes. *)
val character_classes: (string * char array) list

(** [builtin_consts] is an array of the builtin types. *)
val builtin_types: builtin_type array
val is_builtin_type: string -> bool

val mk_builtin_bitwidth: int -> builtin_type

(** [builtin_ops] is an array of the builtin operator symbols. *)
val builtin_ops: builtin_value array

(** [builtin_consts] is an array of the builtin expression identifiers . *)
val builtin_values: builtin_value array
val is_builtin_value: string -> bool

(** [builtin_modules] is a list of the builtin module values. *)
val builtin_modules: builtin_module list
val is_builtin_module: string -> bool

(** [builtin_non_terms] is an array of the builtin non-terminals. *)
val builtin_non_terms: builtin_non_term array
val is_builtin_nonterm: string -> bool

(** predicate for builtin fields *)
val is_builtin_field: string -> bool

(** names of builtin operator constants *)
val unop_const_name: Ast.unop -> string
val binop_const_name: Ast.binop -> string

(** [is_regexp_type env t] checks if [t] is the byte list type used
 ** for regular expressions *)
val is_regexp_type: 'a environment -> 'a CoreAlgebra.arterm -> bool

(** [is_character_class t] checks if [t] is the name of a pre-defined
 ** character class *)
val is_character_class: Ast.ident -> bool

(** checks if a standard library component is a higher-order construct *)
val is_higher_order: Ast.modident * Ast.ident -> bool
