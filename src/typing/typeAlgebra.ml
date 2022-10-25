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
open CoreAlgebra

(** Concrete syntax of a type symbol. *)

type symbol = int

type associativity =
  | Assoc_left
  | Assoc_none
  | Assoc_right
  | Assoc_enclosed of string * string

type syntax =
  (* infix *) bool * associativity * (* priority *) int

type builtin_dataconstructor =
  Ast.dname * Ast.tname list * Ast.type_expr

type builtin_value =
  Ast.vname * Ast.tname list * Ast.type_expr

type builtin_type =
  Ast.tname * (Ast.kind * syntax * builtin_dataconstructor list)

type builtin_non_term =
  Ast.nname * (unit Ast.var * Ast.type_expr * unit) list * Ast.type_expr

type builtin_module =
  {mod_name:   Ast.mod_qual;
   mod_values: builtin_value list}

let builtin_types, builtin_ops, builtin_values,
    builtin_modules, builtin_non_terms =
  let ghost_loc = Location.ghost_loc in
  let stdlib = AstUtils.stdlib in
  let make_var (s: string) =
    Location.mk_ghost (s, ()) in
  let make_builtin_type (t: Ast.type_expr_desc) =
    {Ast.type_expr = t;
     Ast.type_expr_loc = ghost_loc} in
  let arrow_type t1 t2 : Ast.type_expr =
    let tn  = Location.mk_loc_val "->" ghost_loc in
    let con = make_builtin_type (Ast.TE_tname (stdlib, tn)) in
    make_builtin_type (Ast.TE_tapp (con, [ t1; t2 ])) in
  let tuple_type t1 t2 : Ast.type_expr =
    let tn  = Location.mk_loc_val "*" ghost_loc in
    let con = make_builtin_type (Ast.TE_tname (stdlib, tn)) in
    make_builtin_type (Ast.TE_tapp (con, [ t1; t2 ])) in
  let list_type t : Ast.type_expr =
    let tn  = Location.mk_loc_val "[]" ghost_loc in
    let con = make_builtin_type (Ast.TE_tname (stdlib, tn)) in
    make_builtin_type (Ast.TE_tapp (con, [ t ])) in
  let bitvector_type t : Ast.type_expr =
    let tn  = Location.mk_loc_val "bitvector" ghost_loc in
    let con = make_builtin_type (Ast.TE_tname (stdlib, tn)) in
    make_builtin_type (Ast.TE_tapp (con, [ t ])) in
  let opt_type t : Ast.type_expr =
    let tn  = Location.mk_loc_val "option" ghost_loc in
    let con = make_builtin_type (Ast.TE_tname (stdlib, tn)) in
    make_builtin_type (Ast.TE_tapp (con, [ t ])) in
  let set_type t : Ast.type_expr =
    let tn  = Location.mk_loc_val "set" ghost_loc in
    let con = make_builtin_type (Ast.TE_tname (stdlib, tn)) in
    make_builtin_type (Ast.TE_tapp (con, [ t ])) in
  let map_type k v : Ast.type_expr =
    let tn  = Location.mk_loc_val "map" ghost_loc in
    let con = make_builtin_type (Ast.TE_tname (stdlib, tn)) in
    make_builtin_type (Ast.TE_tapp (con, [ k; v ])) in
  let gen_tvar (v: string) : Ast.type_expr =
    let tvar = Location.mk_loc_val v ghost_loc in
    make_builtin_type (Ast.TE_tvar tvar) in
  let gen_tname (t: string) : Ast.type_expr =
    let tn = Location.mk_loc_val t ghost_loc in
    make_builtin_type (Ast.TE_tname (AstUtils.stdlib, tn)) in
  let unit_t   = gen_tname "unit" in
  (* ints, along the lines of Rust *)
  let i8_t     = gen_tname "i8" in
  let i16_t    = gen_tname "i16" in
  let i32_t    = gen_tname "i32" in
  let i64_t    = gen_tname "i64" in
  let isize_t  = gen_tname "isize" in
  let u8_t     = gen_tname "u8" in
  let u16_t    = gen_tname "u16" in
  let u32_t    = gen_tname "u32" in
  let u64_t    = gen_tname "u64" in
  let usize_t  = gen_tname "usize" in
  (* others *)
  let double_t = gen_tname "double" in
  let bool_t   = gen_tname "bool" in
  let bit_t    = gen_tname "bit" in
  let byte_t   = gen_tname "byte" in
  let string_t = gen_tname "string" in
  let endian_t = gen_tname "endian" in
  let view_t   = gen_tname "view" in
  let builtin_types : builtin_type array = [|
      (* core primitive type *)
      TName "->",     (Ast.KArrow (Ast.KStar, Ast.KArrow (Ast.KStar, Ast.KStar)),
                       (true, Assoc_right, 0),
                       []);

      (* value types *)
      TName "*",      (Ast.KArrow (Ast.KStar, Ast.KArrow (Ast.KStar, Ast.KStar)),
                       (true, Assoc_right, 1),
                       [ (Ast.DName "_Tuple", [ TName "a"; TName "b" ],
                          arrow_type (gen_tvar "a")
                            (arrow_type (gen_tvar "b")
                               (tuple_type (gen_tvar "a")
                                  (gen_tvar "b")))) ]);

      TName "[]",     (Ast.KArrow (Ast.KStar, Ast.KStar),
                       (false, Assoc_enclosed ("[", "]"), -1),
                       [ (Ast.DName "::", [ TName "a" ],
                          arrow_type (gen_tvar "a")
                            (arrow_type (list_type (gen_tvar "a"))
                               (list_type (gen_tvar "a"))));
                         (Ast.DName "[]", [ TName "a" ],
                          list_type (gen_tvar "a")) ]);
      TName "option", (Ast.KArrow (Ast.KStar, Ast.KStar),
                       (false, Assoc_enclosed ("option<", ">"), 1),
                       [ (Ast.DName "None", [ TName "a" ],
                          opt_type (gen_tvar "a"));
                         (Ast.DName "Some", [ TName "a" ],
                          arrow_type (gen_tvar "a")
                            (opt_type (gen_tvar "a"))) ]);
      TName "i8",     (Ast.KStar, (false, Assoc_none, 2), []);
      TName "i16",    (Ast.KStar, (false, Assoc_none, 2), []);
      TName "i32",    (Ast.KStar, (false, Assoc_none, 2), []);
      TName "i64",    (Ast.KStar, (false, Assoc_none, 2), []);
      TName "u8",     (Ast.KStar, (false, Assoc_none, 2), []);
      TName "u16",    (Ast.KStar, (false, Assoc_none, 2), []);
      TName "u32",    (Ast.KStar, (false, Assoc_none, 2), []);
      TName "u64",    (Ast.KStar, (false, Assoc_none, 2), []);
      TName "isize",  (Ast.KStar, (false, Assoc_none, 2), []);
      TName "usize",  (Ast.KStar, (false, Assoc_none, 2), []);
      TName "double", (Ast.KStar, (false, Assoc_none, 2), []);
      TName "char",   (Ast.KStar, (false, Assoc_none, 2), []);
      TName "byte",   (Ast.KStar, (false, Assoc_none, 2), []);
      TName "string", (Ast.KStar, (false, Assoc_none, 2), []);
      TName "unit",   (Ast.KStar,
                       (false, Assoc_none, 2),
                       [ (Ast.DName "_Unit", [], unit_t) ]);
      TName "bool",   (Ast.KStar,
                       (false, Assoc_none, 2),
                       [ (Ast.DName "True",  [], bool_t);
                         (Ast.DName "False", [], bool_t) ]);
      TName "endian", (Ast.KStar,
                       (false, Assoc_none, 2),
                       [ (Ast.DName "Big", [], endian_t);
                         (Ast.DName "Little", [], endian_t) ]);
      TName "bit",    (Ast.KStar,
                       (false, Assoc_none, 2),
                       [ (Ast.DName "One",  [], bit_t);
                         (Ast.DName "Zero", [], bit_t) ]);
      TName "bitvector", (Ast.KArrow (Ast.KNat, Ast.KStar),
                          (false, Assoc_enclosed ("bitvector<", ">"), 2),
                          []);
      (* module types *)
      TName "view",   (Ast.KStar, (false, Assoc_none, 2), []);
      TName "set",    ((Ast.KArrow (Ast.KStar, Ast.KStar)),
                       (false, Assoc_enclosed ("set<", ">"), 2),
                       []);
      TName "map",    ((Ast.KArrow
                          (Ast.KStar,
                           (Ast.KArrow (Ast.KStar, Ast.KStar)))),
                       (false, Assoc_enclosed ("map<", ">"), 2),
                       []);
    |] in
  (* When adding new builtins, please also add their implementations
     to builtins.ml *)
  let builtin_ops : builtin_value array = [|
      (Ast.VName "1-_i",   [], arrow_type isize_t isize_t);
      (Ast.VName "1-_i8",  [], arrow_type i8_t i8_t);
      (Ast.VName "1-_i16", [], arrow_type i16_t i16_t);
      (Ast.VName "1-_i32", [], arrow_type i32_t i32_t);
      (Ast.VName "1-_i64", [], arrow_type i64_t i64_t);
      (Ast.VName "1-_u",   [], arrow_type usize_t usize_t);
      (Ast.VName "1-_u8",  [], arrow_type u8_t u8_t);
      (Ast.VName "1-_u16", [], arrow_type u16_t u16_t);
      (Ast.VName "1-_u32", [], arrow_type u32_t u32_t);
      (Ast.VName "1-_u64", [], arrow_type u64_t u64_t);

      (Ast.VName "!",  [], arrow_type bool_t bool_t);

      (Ast.VName "+_i",  [], arrow_type isize_t (arrow_type isize_t isize_t));
      (Ast.VName "-_i",  [], arrow_type isize_t (arrow_type isize_t isize_t));
      (Ast.VName "*_i",  [], arrow_type isize_t (arrow_type isize_t isize_t));
      (Ast.VName "/_i",  [], arrow_type isize_t (arrow_type isize_t isize_t));
      (Ast.VName "%_i",  [], arrow_type isize_t (arrow_type isize_t isize_t));

      (Ast.VName "<_i",  [], arrow_type isize_t (arrow_type isize_t bool_t));
      (Ast.VName ">_i",  [], arrow_type isize_t (arrow_type isize_t bool_t));
      (Ast.VName "<=_i", [], arrow_type isize_t (arrow_type isize_t bool_t));
      (Ast.VName ">=_i", [], arrow_type isize_t (arrow_type isize_t bool_t));

      (Ast.VName "~_i",  [], arrow_type isize_t isize_t);
      (Ast.VName "&_i",  [], arrow_type isize_t (arrow_type isize_t isize_t));
      (Ast.VName "|_i",  [], arrow_type isize_t (arrow_type isize_t isize_t));
      (Ast.VName "^_i",  [], arrow_type isize_t (arrow_type isize_t isize_t));

      (Ast.VName "<<_i",  [], arrow_type isize_t (arrow_type u8_t isize_t));
      (Ast.VName ">>_i",  [], arrow_type isize_t (arrow_type u8_t isize_t));
      (Ast.VName ">>_ai", [], arrow_type isize_t (arrow_type u8_t isize_t));

      (Ast.VName "+_i8",  [], arrow_type i8_t (arrow_type i8_t i8_t));
      (Ast.VName "-_i8",  [], arrow_type i8_t (arrow_type i8_t i8_t));
      (Ast.VName "*_i8",  [], arrow_type i8_t (arrow_type i8_t i8_t));
      (Ast.VName "/_i8",  [], arrow_type i8_t (arrow_type i8_t i8_t));
      (Ast.VName "%_i8",  [], arrow_type i8_t (arrow_type i8_t i8_t));

      (Ast.VName "<_i8",  [], arrow_type i8_t (arrow_type i8_t bool_t));
      (Ast.VName ">_i8",  [], arrow_type i8_t (arrow_type i8_t bool_t));
      (Ast.VName "<=_i8", [], arrow_type i8_t (arrow_type i8_t bool_t));
      (Ast.VName ">=_i8", [], arrow_type i8_t (arrow_type i8_t bool_t));

      (Ast.VName "~_i8",  [], arrow_type i8_t i8_t);
      (Ast.VName "&_i8",  [], arrow_type i8_t (arrow_type i8_t i8_t));
      (Ast.VName "|_i8",  [], arrow_type i8_t (arrow_type i8_t i8_t));
      (Ast.VName "^_i8",  [], arrow_type i8_t (arrow_type i8_t i8_t));

      (Ast.VName "<<_i8",  [], arrow_type i8_t (arrow_type u8_t i8_t));
      (Ast.VName ">>_i8",  [], arrow_type i8_t (arrow_type u8_t i8_t));
      (Ast.VName ">>_ai8", [], arrow_type i8_t (arrow_type u8_t i8_t));

      (Ast.VName "+_i16",  [], arrow_type i16_t (arrow_type i16_t i16_t));
      (Ast.VName "-_i16",  [], arrow_type i16_t (arrow_type i16_t i16_t));
      (Ast.VName "*_i16",  [], arrow_type i16_t (arrow_type i16_t i16_t));
      (Ast.VName "/_i16",  [], arrow_type i16_t (arrow_type i16_t i16_t));
      (Ast.VName "%_i16",  [], arrow_type i16_t (arrow_type i16_t i16_t));

      (Ast.VName "<_i16",  [], arrow_type i16_t (arrow_type i16_t bool_t));
      (Ast.VName ">_i16",  [], arrow_type i16_t (arrow_type i16_t bool_t));
      (Ast.VName "<=_i16", [], arrow_type i16_t (arrow_type i16_t bool_t));
      (Ast.VName ">=_i16", [], arrow_type i16_t (arrow_type i16_t bool_t));

      (Ast.VName "~_i16",  [], arrow_type i16_t i16_t);
      (Ast.VName "&_i16",  [], arrow_type i16_t (arrow_type i16_t i16_t));
      (Ast.VName "|_i16",  [], arrow_type i16_t (arrow_type i16_t i16_t));
      (Ast.VName "^_i16",  [], arrow_type i16_t (arrow_type i16_t i16_t));

      (Ast.VName "<<_i16", [], arrow_type i16_t (arrow_type u8_t i16_t));
      (Ast.VName ">>_i16", [], arrow_type i16_t (arrow_type u8_t i16_t));
      (Ast.VName ">>_ai16",[], arrow_type i16_t (arrow_type u8_t i16_t));

      (Ast.VName "+_i32",  [], arrow_type i32_t (arrow_type i32_t i32_t));
      (Ast.VName "-_i32",  [], arrow_type i32_t (arrow_type i32_t i32_t));
      (Ast.VName "*_i32",  [], arrow_type i32_t (arrow_type i32_t i32_t));
      (Ast.VName "/_i32",  [], arrow_type i32_t (arrow_type i32_t i32_t));
      (Ast.VName "%_i32",  [], arrow_type i32_t (arrow_type i32_t i32_t));

      (Ast.VName "<_i32",  [], arrow_type i32_t (arrow_type i32_t bool_t));
      (Ast.VName ">_i32",  [], arrow_type i32_t (arrow_type i32_t bool_t));
      (Ast.VName "<=_i32", [], arrow_type i32_t (arrow_type i32_t bool_t));
      (Ast.VName ">=_i32", [], arrow_type i32_t (arrow_type i32_t bool_t));

      (Ast.VName "~_i32",  [], arrow_type i32_t i32_t);
      (Ast.VName "&_i32",  [], arrow_type i32_t (arrow_type i32_t i32_t));
      (Ast.VName "|_i32",  [], arrow_type i32_t (arrow_type i32_t i32_t));
      (Ast.VName "^_i32",  [], arrow_type i32_t (arrow_type i32_t i32_t));

      (Ast.VName "<<_i32", [], arrow_type i32_t (arrow_type u8_t i32_t));
      (Ast.VName ">>_i32", [], arrow_type i32_t (arrow_type u8_t i32_t));
      (Ast.VName ">>_ai32",[], arrow_type i32_t (arrow_type u8_t i32_t));

      (Ast.VName "+_i64",  [], arrow_type i64_t (arrow_type i64_t i64_t));
      (Ast.VName "-_i64",  [], arrow_type i64_t (arrow_type i64_t i64_t));
      (Ast.VName "*_i64",  [], arrow_type i64_t (arrow_type i64_t i64_t));
      (Ast.VName "/_i64",  [], arrow_type i64_t (arrow_type i64_t i64_t));
      (Ast.VName "%_i64",  [], arrow_type i64_t (arrow_type i64_t i64_t));

      (Ast.VName "<_i64",  [], arrow_type i64_t (arrow_type i64_t bool_t));
      (Ast.VName ">_i64",  [], arrow_type i64_t (arrow_type i64_t bool_t));
      (Ast.VName "<=_i64", [], arrow_type i64_t (arrow_type i64_t bool_t));
      (Ast.VName ">=_i64", [], arrow_type i64_t (arrow_type i64_t bool_t));

      (Ast.VName "~_i64",  [], arrow_type i64_t i64_t);
      (Ast.VName "&_i64",  [], arrow_type i64_t (arrow_type i64_t i64_t));
      (Ast.VName "|_i64",  [], arrow_type i64_t (arrow_type i64_t i64_t));
      (Ast.VName "^_i64",  [], arrow_type i64_t (arrow_type i64_t i64_t));

      (Ast.VName "<<_i64", [], arrow_type i64_t (arrow_type u8_t i64_t));
      (Ast.VName ">>_i64", [], arrow_type i64_t (arrow_type u8_t i64_t));
      (Ast.VName ">>_ai64",[], arrow_type i64_t (arrow_type u8_t i64_t));

      (Ast.VName "+_u",  [], arrow_type usize_t (arrow_type usize_t usize_t));
      (Ast.VName "-_u",  [], arrow_type usize_t (arrow_type usize_t usize_t));
      (Ast.VName "*_u",  [], arrow_type usize_t (arrow_type usize_t usize_t));
      (Ast.VName "/_u",  [], arrow_type usize_t (arrow_type usize_t usize_t));
      (Ast.VName "%_u",  [], arrow_type usize_t (arrow_type usize_t usize_t));

      (Ast.VName "<_u",  [], arrow_type usize_t (arrow_type usize_t bool_t));
      (Ast.VName ">_u",  [], arrow_type usize_t (arrow_type usize_t bool_t));
      (Ast.VName "<=_u", [], arrow_type usize_t (arrow_type usize_t bool_t));
      (Ast.VName ">=_u", [], arrow_type usize_t (arrow_type usize_t bool_t));

      (Ast.VName "~_u",  [], arrow_type usize_t usize_t);
      (Ast.VName "&_u",  [], arrow_type usize_t (arrow_type usize_t usize_t));
      (Ast.VName "|_u",  [], arrow_type usize_t (arrow_type usize_t usize_t));
      (Ast.VName "^_u",  [], arrow_type usize_t (arrow_type usize_t usize_t));

      (Ast.VName "<<_u",  [], arrow_type usize_t (arrow_type u8_t usize_t));
      (Ast.VName ">>_u",  [], arrow_type usize_t (arrow_type u8_t usize_t));
      (Ast.VName ">>_au", [], arrow_type usize_t (arrow_type u8_t usize_t));

      (Ast.VName "+_u8",  [], arrow_type u8_t (arrow_type u8_t u8_t));
      (Ast.VName "-_u8",  [], arrow_type u8_t (arrow_type u8_t u8_t));
      (Ast.VName "*_u8",  [], arrow_type u8_t (arrow_type u8_t u8_t));
      (Ast.VName "/_u8",  [], arrow_type u8_t (arrow_type u8_t u8_t));
      (Ast.VName "%_u8",  [], arrow_type u8_t (arrow_type u8_t u8_t));

      (Ast.VName "<_u8",  [], arrow_type u8_t (arrow_type u8_t bool_t));
      (Ast.VName ">_u8",  [], arrow_type u8_t (arrow_type u8_t bool_t));
      (Ast.VName "<=_u8", [], arrow_type u8_t (arrow_type u8_t bool_t));
      (Ast.VName ">=_u8", [], arrow_type u8_t (arrow_type u8_t bool_t));

      (Ast.VName "~_u8",  [], arrow_type u8_t u8_t);
      (Ast.VName "&_u8",  [], arrow_type u8_t (arrow_type u8_t u8_t));
      (Ast.VName "|_u8",  [], arrow_type u8_t (arrow_type u8_t u8_t));
      (Ast.VName "^_u8",  [], arrow_type u8_t (arrow_type u8_t u8_t));

      (Ast.VName "<<_u8",  [], arrow_type u8_t (arrow_type u8_t u8_t));
      (Ast.VName ">>_u8",  [], arrow_type u8_t (arrow_type u8_t u8_t));
      (Ast.VName ">>_au8", [], arrow_type u8_t (arrow_type u8_t u8_t));

      (Ast.VName "+_u16",  [], arrow_type u16_t (arrow_type u16_t u16_t));
      (Ast.VName "-_u16",  [], arrow_type u16_t (arrow_type u16_t u16_t));
      (Ast.VName "*_u16",  [], arrow_type u16_t (arrow_type u16_t u16_t));
      (Ast.VName "/_u16",  [], arrow_type u16_t (arrow_type u16_t u16_t));
      (Ast.VName "%_u16",  [], arrow_type u16_t (arrow_type u16_t u16_t));

      (Ast.VName "<_u16",  [], arrow_type u16_t (arrow_type u16_t bool_t));
      (Ast.VName ">_u16",  [], arrow_type u16_t (arrow_type u16_t bool_t));
      (Ast.VName "<=_u16", [], arrow_type u16_t (arrow_type u16_t bool_t));
      (Ast.VName ">=_u16", [], arrow_type u16_t (arrow_type u16_t bool_t));

      (Ast.VName "~_u16",  [], arrow_type u16_t u16_t);
      (Ast.VName "&_u16",  [], arrow_type u16_t (arrow_type u16_t u16_t));
      (Ast.VName "|_u16",  [], arrow_type u16_t (arrow_type u16_t u16_t));
      (Ast.VName "^_u16",  [], arrow_type u16_t (arrow_type u16_t u16_t));

      (Ast.VName "<<_u16", [], arrow_type u16_t (arrow_type u8_t u16_t));
      (Ast.VName ">>_u16", [], arrow_type u16_t (arrow_type u8_t u16_t));
      (Ast.VName ">>_au16",[], arrow_type u16_t (arrow_type u8_t u16_t));

      (Ast.VName "+_u32",  [], arrow_type u32_t (arrow_type u32_t u32_t));
      (Ast.VName "-_u32",  [], arrow_type u32_t (arrow_type u32_t u32_t));
      (Ast.VName "*_u32",  [], arrow_type u32_t (arrow_type u32_t u32_t));
      (Ast.VName "/_u32",  [], arrow_type u32_t (arrow_type u32_t u32_t));
      (Ast.VName "%_u32",  [], arrow_type u32_t (arrow_type u32_t u32_t));

      (Ast.VName "<_u32",  [], arrow_type u32_t (arrow_type u32_t bool_t));
      (Ast.VName ">_u32",  [], arrow_type u32_t (arrow_type u32_t bool_t));
      (Ast.VName "<=_u32", [], arrow_type u32_t (arrow_type u32_t bool_t));
      (Ast.VName ">=_u32", [], arrow_type u32_t (arrow_type u32_t bool_t));

      (Ast.VName "~_u32",  [], arrow_type u32_t u32_t);
      (Ast.VName "&_u32",  [], arrow_type u32_t (arrow_type u32_t u32_t));
      (Ast.VName "|_u32",  [], arrow_type u32_t (arrow_type u32_t u32_t));
      (Ast.VName "^_u32",  [], arrow_type u32_t (arrow_type u32_t u32_t));

      (Ast.VName "<<_u32", [], arrow_type u32_t (arrow_type u8_t u32_t));
      (Ast.VName ">>_u32", [], arrow_type u32_t (arrow_type u8_t u32_t));
      (Ast.VName ">>_au32",[], arrow_type u32_t (arrow_type u8_t u32_t));

      (Ast.VName "+_u64",  [], arrow_type u64_t (arrow_type u64_t u64_t));
      (Ast.VName "-_u64",  [], arrow_type u64_t (arrow_type u64_t u64_t));
      (Ast.VName "*_u64",  [], arrow_type u64_t (arrow_type u64_t u64_t));
      (Ast.VName "/_u64",  [], arrow_type u64_t (arrow_type u64_t u64_t));
      (Ast.VName "%_u64",  [], arrow_type u64_t (arrow_type u64_t u64_t));

      (Ast.VName "<_u64",  [], arrow_type u64_t (arrow_type u64_t bool_t));
      (Ast.VName ">_u64",  [], arrow_type u64_t (arrow_type u64_t bool_t));
      (Ast.VName "<=_u64", [], arrow_type u64_t (arrow_type u64_t bool_t));
      (Ast.VName ">=_u64", [], arrow_type u64_t (arrow_type u64_t bool_t));

      (Ast.VName "~_u64",  [], arrow_type u64_t u64_t);
      (Ast.VName "&_u64",  [], arrow_type u64_t (arrow_type u64_t u64_t));
      (Ast.VName "|_u64",  [], arrow_type u64_t (arrow_type u64_t u64_t));
      (Ast.VName "^_u64",  [], arrow_type u64_t (arrow_type u64_t u64_t));

      (Ast.VName "<<_u64", [], arrow_type u64_t (arrow_type u8_t u64_t));
      (Ast.VName ">>_u64", [], arrow_type u64_t (arrow_type u8_t u64_t));
      (Ast.VName ">>_au64",[], arrow_type u64_t (arrow_type u8_t u64_t));

      (Ast.VName "&&", [], arrow_type bool_t (arrow_type bool_t bool_t));
      (Ast.VName "||", [], arrow_type bool_t (arrow_type bool_t bool_t));

      (Ast.VName "~",  [ TName "a" ], arrow_type (bitvector_type (gen_tvar "a"))
                                           (bitvector_type (gen_tvar "a")));
      (Ast.VName "|_b",  [ TName "a" ], arrow_type (bitvector_type (gen_tvar "a"))
                                          (arrow_type (bitvector_type (gen_tvar "a"))
                                             (bitvector_type (gen_tvar "a"))));
      (Ast.VName "&_b",  [ TName "a" ], arrow_type (bitvector_type (gen_tvar "a"))
                                          (arrow_type (bitvector_type (gen_tvar "a"))
                                             (bitvector_type (gen_tvar "a"))));

      (Ast.VName "=",  [ TName "a" ], arrow_type (gen_tvar "a")
                                        (arrow_type (gen_tvar "a") bool_t));
      (Ast.VName "!=", [ TName "a" ], arrow_type (gen_tvar "a")
                                        (arrow_type (gen_tvar "a") bool_t));

      (Ast.VName ".[]", [ TName "a" ], arrow_type (list_type (gen_tvar "a"))
                                        (arrow_type usize_t
                                           (opt_type (gen_tvar "a"))));
    |] in
  let builtin_values : builtin_value array = [|
    |] in

  (* When adding modules or functions below, please also add their
     implementations to parsleylib.ml *)
  let builtin_modules : builtin_module list = [
      {mod_name   = Ast.Mod_inferred "Byte";
       mod_values = [
           (* checked conversions *)
           (Ast.VName "of_i8", [],
            arrow_type i8_t (opt_type byte_t));
           (Ast.VName "of_u8", [],
            arrow_type u8_t (opt_type byte_t));
           (Ast.VName "of_i16", [],
            arrow_type i16_t (opt_type byte_t));
           (Ast.VName "of_u16", [],
            arrow_type u16_t (opt_type byte_t));
           (Ast.VName "of_i32", [],
            arrow_type i32_t (opt_type byte_t));
           (Ast.VName "of_u32", [],
            arrow_type u32_t (opt_type byte_t));
           (Ast.VName "of_i64", [],
            arrow_type i64_t (opt_type byte_t));
           (Ast.VName "of_u64", [],
            arrow_type u64_t (opt_type byte_t));
           (Ast.VName "of_isize", [],
            arrow_type isize_t (opt_type byte_t));
           (Ast.VName "of_usize", [],
            arrow_type usize_t (opt_type byte_t));

           (* wrapped conversions *)
           (Ast.VName "of_i8_wrapped", [],
            arrow_type i8_t byte_t);
           (Ast.VName "of_u8_wrapped", [],
            arrow_type u8_t byte_t);
           (Ast.VName "of_i16_wrapped", [],
            arrow_type i16_t byte_t);
           (Ast.VName "of_u16_wrapped", [],
            arrow_type u16_t byte_t);
           (Ast.VName "of_i32_wrapped", [],
            arrow_type i32_t byte_t);
           (Ast.VName "of_u32_wrapped", [],
            arrow_type u32_t byte_t);
           (Ast.VName "of_i64_wrapped", [],
            arrow_type i64_t byte_t);
           (Ast.VName "of_u64_wrapped", [],
            arrow_type u64_t byte_t);
           (Ast.VName "of_isize_wrapped", [],
            arrow_type isize_t byte_t);
           (Ast.VName "of_usize_wrapped", [],
            arrow_type usize_t byte_t);

           (Ast.VName "to_isize", [],
            arrow_type byte_t isize_t);
           (Ast.VName "to_i8", [],
            arrow_type byte_t i8_t);
           (Ast.VName "to_i16", [],
            arrow_type byte_t i16_t);
           (Ast.VName "to_i32", [],
            arrow_type byte_t i32_t);
           (Ast.VName "to_i64", [],
            arrow_type byte_t i64_t);
           (Ast.VName "to_usize", [],
            arrow_type byte_t usize_t);
           (Ast.VName "to_u8", [],
            arrow_type byte_t u8_t);
           (Ast.VName "to_u16", [],
            arrow_type byte_t u16_t);
           (Ast.VName "to_u32", [],
            arrow_type byte_t u32_t);
           (Ast.VName "to_u64", [],
            arrow_type byte_t u64_t);
         ];
      };
      {mod_name   = Ast.Mod_inferred "I8";
       mod_values = [
           (Ast.VName "of_byte", [],
            arrow_type byte_t (opt_type i8_t));
           (Ast.VName "of_string", [],
            arrow_type string_t (opt_type i8_t));
           (Ast.VName "of_string_unsafe", [],
            arrow_type string_t i8_t);
           (Ast.VName "of_i16", [],
            arrow_type i16_t (opt_type i8_t));
           (Ast.VName "of_i32", [],
            arrow_type i32_t (opt_type i8_t));
           (Ast.VName "of_i64", [],
            arrow_type i64_t (opt_type i8_t));
           (Ast.VName "of_isize", [],
            arrow_type isize_t (opt_type i8_t));
           (Ast.VName "of_u8", [],
            arrow_type u8_t  (opt_type i8_t));
           (Ast.VName "of_u16", [],
            arrow_type u16_t (opt_type i8_t));
           (Ast.VName "of_u32", [],
            arrow_type u32_t (opt_type i8_t));
           (Ast.VName "of_u64", [],
            arrow_type u64_t (opt_type i8_t));
           (Ast.VName "of_usize", [],
            arrow_type usize_t (opt_type i8_t));
           (Ast.VName "of_i16_wrapped", [],
            arrow_type i16_t i8_t);
           (Ast.VName "of_i32_wrapped", [],
            arrow_type i32_t i8_t);
           (Ast.VName "of_i64_wrapped", [],
            arrow_type i64_t i8_t);
           (Ast.VName "of_isize_wrapped", [],
            arrow_type isize_t i8_t);
           (Ast.VName "of_u8_wrapped", [],
            arrow_type u8_t  i8_t);
           (Ast.VName "of_u16_wrapped", [],
            arrow_type u16_t i8_t);
           (Ast.VName "of_u32_wrapped", [],
            arrow_type u32_t i8_t);
           (Ast.VName "of_u64_wrapped", [],
            arrow_type u64_t i8_t);
           (Ast.VName "of_usize_wrapped", [],
            arrow_type usize_t i8_t);
         ];
      };
      {mod_name   = Ast.Mod_inferred "U8";
       mod_values = [
           (Ast.VName "of_byte", [],
            arrow_type byte_t u8_t);
           (Ast.VName "of_string", [],
            arrow_type string_t (opt_type u8_t));
           (Ast.VName "of_string_unsafe", [],
            arrow_type string_t u8_t);
           (Ast.VName "of_i8", [],
            arrow_type i8_t  (opt_type u8_t));
           (Ast.VName "of_i16", [],
            arrow_type i16_t (opt_type u8_t));
           (Ast.VName "of_i32", [],
            arrow_type i32_t (opt_type u8_t));
           (Ast.VName "of_i64", [],
            arrow_type i64_t (opt_type u8_t));
           (Ast.VName "of_isize", [],
            arrow_type isize_t (opt_type u8_t));
           (Ast.VName "of_u16", [],
            arrow_type u16_t (opt_type u8_t));
           (Ast.VName "of_u32", [],
            arrow_type u32_t (opt_type u8_t));
           (Ast.VName "of_u64", [],
            arrow_type u64_t (opt_type u8_t));
           (Ast.VName "of_usize", [],
            arrow_type usize_t (opt_type u8_t));
           (Ast.VName "of_i8_wrapped", [],
            arrow_type i8_t  u8_t);
           (Ast.VName "of_i16_wrapped", [],
            arrow_type i16_t u8_t);
           (Ast.VName "of_i32_wrapped", [],
            arrow_type i32_t u8_t);
           (Ast.VName "of_i64_wrapped", [],
            arrow_type i64_t u8_t);
           (Ast.VName "of_isize_wrapped", [],
            arrow_type isize_t u8_t);
           (Ast.VName "of_u16_wrapped", [],
            arrow_type u16_t u8_t);
           (Ast.VName "of_u32_wrapped", [],
            arrow_type u32_t u8_t);
           (Ast.VName "of_u64_wrapped", [],
            arrow_type u64_t u8_t);
           (Ast.VName "of_usize_wrapped", [],
            arrow_type usize_t u8_t);
         ];
      };
      {mod_name   = Ast.Mod_inferred "I16";
       mod_values = [
           (Ast.VName "of_byte", [],
            arrow_type byte_t i16_t);
           (Ast.VName "of_bytes", [],
            arrow_type (list_type byte_t) (opt_type i16_t));
           (Ast.VName "of_bytes_unsafe", [],
            arrow_type (list_type byte_t) i16_t);
           (Ast.VName "of_string", [],
            arrow_type string_t (opt_type i16_t));
           (Ast.VName "of_string_unsafe", [],
            arrow_type string_t i16_t);
           (Ast.VName "of_i8", [],
            arrow_type i8_t  i16_t);
           (Ast.VName "of_i32", [],
            arrow_type i32_t (opt_type i16_t));
           (Ast.VName "of_i64", [],
            arrow_type i64_t (opt_type i16_t));
           (Ast.VName "of_isize", [],
            arrow_type isize_t (opt_type i16_t));
           (Ast.VName "of_u8", [],
            arrow_type u8_t  i16_t);
           (Ast.VName "of_u16", [],
            arrow_type u16_t (opt_type i16_t));
           (Ast.VName "of_u32", [],
            arrow_type u32_t (opt_type i16_t));
           (Ast.VName "of_u64", [],
            arrow_type u64_t (opt_type i16_t));
           (Ast.VName "of_usize", [],
            arrow_type usize_t (opt_type i16_t));
           (Ast.VName "of_i32_wrapped", [],
            arrow_type i32_t i16_t);
           (Ast.VName "of_i64_wrapped", [],
            arrow_type i64_t i16_t);
           (Ast.VName "of_isize_wrapped", [],
            arrow_type isize_t i16_t);
           (Ast.VName "of_u16_wrapped", [],
            arrow_type u16_t i16_t);
           (Ast.VName "of_u32_wrapped", [],
            arrow_type u32_t i16_t);
           (Ast.VName "of_u64_wrapped", [],
            arrow_type u64_t i16_t);
           (Ast.VName "of_usize_wrapped", [],
            arrow_type usize_t i16_t);
         ];
      };
      {mod_name   = Ast.Mod_inferred "U16";
       mod_values = [
           (Ast.VName "of_byte", [],
            arrow_type byte_t u16_t);
           (Ast.VName "of_bytes", [],
            arrow_type (list_type byte_t) (opt_type u16_t));
           (Ast.VName "of_bytes_unsafe", [],
            arrow_type (list_type byte_t) u16_t);
           (Ast.VName "of_string", [],
            arrow_type string_t (opt_type u16_t));
           (Ast.VName "of_string_unsafe", [],
            arrow_type string_t u16_t);
           (Ast.VName "of_i8", [],
            arrow_type i8_t  (opt_type u16_t));
           (Ast.VName "of_i16", [],
            arrow_type i16_t (opt_type u16_t));
           (Ast.VName "of_i32", [],
            arrow_type i32_t (opt_type u16_t));
           (Ast.VName "of_i64", [],
            arrow_type i64_t (opt_type u16_t));
           (Ast.VName "of_isize", [],
            arrow_type isize_t (opt_type u16_t));
           (Ast.VName "of_u8", [],
            arrow_type u8_t  u16_t);
           (Ast.VName "of_u32", [],
            arrow_type u32_t (opt_type u16_t));
           (Ast.VName "of_u64", [],
            arrow_type u64_t (opt_type u16_t));
           (Ast.VName "of_usize", [],
            arrow_type usize_t (opt_type u16_t));
           (Ast.VName "of_i8_wrapped", [],
            arrow_type i8_t  u16_t);
           (Ast.VName "of_i16_wrapped", [],
            arrow_type i16_t u16_t);
           (Ast.VName "of_i32_wrapped", [],
            arrow_type i32_t u16_t);
           (Ast.VName "of_i64_wrapped", [],
            arrow_type i64_t u16_t);
           (Ast.VName "of_isize_wrapped", [],
            arrow_type isize_t u16_t);
           (Ast.VName "of_u32_wrapped", [],
            arrow_type u32_t u16_t);
           (Ast.VName "of_u64_wrapped", [],
            arrow_type u64_t u16_t);
           (Ast.VName "of_usize_wrapped", [],
            arrow_type usize_t u16_t);
         ];
      };
      {mod_name   = Ast.Mod_inferred "I32";
       mod_values = [
           (Ast.VName "of_byte", [],
            arrow_type byte_t i32_t);
           (Ast.VName "of_bytes", [],
            arrow_type (list_type byte_t) (opt_type i32_t));
           (Ast.VName "of_bytes_unsafe", [],
            arrow_type (list_type byte_t) i32_t);
           (Ast.VName "of_string", [],
            arrow_type string_t (opt_type i32_t));
           (Ast.VName "of_string_unsafe", [],
            arrow_type string_t i32_t);
           (Ast.VName "of_i8", [],
            arrow_type i8_t  i32_t);
           (Ast.VName "of_i16", [],
            arrow_type i16_t i32_t);
           (Ast.VName "of_i64", [],
            arrow_type i64_t (opt_type i32_t));
           (Ast.VName "of_isize", [],
            arrow_type isize_t (opt_type i32_t));
           (Ast.VName "of_u8", [],
            arrow_type u8_t  i32_t);
           (Ast.VName "of_u16", [],
            arrow_type u16_t i32_t);
           (Ast.VName "of_u32", [],
            arrow_type u32_t (opt_type i32_t));
           (Ast.VName "of_u64", [],
            arrow_type u64_t (opt_type i32_t));
           (Ast.VName "of_usize", [],
            arrow_type usize_t (opt_type i32_t));
           (Ast.VName "of_i64_wrapped", [],
            arrow_type i64_t i32_t);
           (Ast.VName "of_isize_wrapped", [],
            arrow_type isize_t i32_t);
           (Ast.VName "of_u32_wrapped", [],
            arrow_type u32_t i32_t);
           (Ast.VName "of_u64_wrapped", [],
            arrow_type u64_t i32_t);
           (Ast.VName "of_usize_wrapped", [],
            arrow_type usize_t i32_t);
         ];
      };
      {mod_name   = Ast.Mod_inferred "U32";
       mod_values = [
           (Ast.VName "of_byte", [],
            arrow_type byte_t u32_t);
           (Ast.VName "of_bytes", [],
            arrow_type (list_type byte_t) (opt_type u32_t));
           (Ast.VName "of_bytes_unsafe", [],
            arrow_type (list_type byte_t) u32_t);
           (Ast.VName "of_string", [],
            arrow_type string_t (opt_type u32_t));
           (Ast.VName "of_string_unsafe", [],
            arrow_type string_t u32_t);
           (Ast.VName "of_i8", [],
            arrow_type i8_t  (opt_type u32_t));
           (Ast.VName "of_i16", [],
            arrow_type i16_t (opt_type u32_t));
           (Ast.VName "of_i32", [],
            arrow_type i32_t (opt_type u32_t));
           (Ast.VName "of_i64", [],
            arrow_type i64_t (opt_type u32_t));
           (Ast.VName "of_isize", [],
            arrow_type isize_t (opt_type u32_t));
           (Ast.VName "of_u8", [],
            arrow_type u8_t  u32_t);
           (Ast.VName "of_u16", [],
            arrow_type u16_t u32_t);
           (Ast.VName "of_u64", [],
            arrow_type u64_t (opt_type u32_t));
           (Ast.VName "of_usize", [],
            arrow_type usize_t (opt_type u32_t));
           (Ast.VName "of_i8_wrapped", [],
            arrow_type i8_t  u32_t);
           (Ast.VName "of_i16_wrapped", [],
            arrow_type i16_t u32_t);
           (Ast.VName "of_i32_wrapped", [],
            arrow_type i32_t u32_t);
           (Ast.VName "of_i64_wrapped", [],
            arrow_type i64_t u32_t);
           (Ast.VName "of_isize_wrapped", [],
            arrow_type isize_t u32_t);
           (Ast.VName "of_u64_wrapped", [],
            arrow_type u64_t u32_t);
           (Ast.VName "of_usize_wrapped", [],
            arrow_type usize_t u32_t);
         ];
      };
      {mod_name   = Ast.Mod_inferred "I64";
       mod_values = [
           (Ast.VName "of_byte", [],
            arrow_type byte_t i64_t);
           (Ast.VName "of_bytes", [],
            arrow_type (list_type byte_t) (opt_type i64_t));
           (Ast.VName "of_bytes_unsafe", [],
            arrow_type (list_type byte_t) i64_t);
           (Ast.VName "of_string", [],
            arrow_type string_t (opt_type i64_t));
           (Ast.VName "of_string_unsafe", [],
            arrow_type string_t i64_t);
           (Ast.VName "of_i8", [],
            arrow_type i8_t  i64_t);
           (Ast.VName "of_i16", [],
            arrow_type i16_t i64_t);
           (Ast.VName "of_i32", [],
            arrow_type i32_t i64_t);
           (Ast.VName "of_isize", [],
            arrow_type isize_t (opt_type i64_t));
           (Ast.VName "of_u8", [],
            arrow_type u8_t  i64_t);
           (Ast.VName "of_u16", [],
            arrow_type u16_t i64_t);
           (Ast.VName "of_u32", [],
            arrow_type u32_t i64_t);
           (Ast.VName "of_u64", [],
            arrow_type u64_t (opt_type i64_t));
           (Ast.VName "of_usize", [],
            arrow_type usize_t (opt_type i64_t));
           (Ast.VName "of_u64_wrapped", [],
            arrow_type u64_t i64_t);
           (Ast.VName "of_isize_wrapped", [],
            arrow_type isize_t i64_t);
           (Ast.VName "of_usize_wrapped", [],
            arrow_type usize_t i64_t);
         ];
      };
      {mod_name   = Ast.Mod_inferred "Isize";
       mod_values = [
           (Ast.VName "of_byte", [],
            arrow_type byte_t isize_t);
           (Ast.VName "of_bytes", [],
            arrow_type (list_type byte_t) (opt_type isize_t));
           (Ast.VName "of_bytes_unsafe", [],
            arrow_type (list_type byte_t) isize_t);
           (Ast.VName "of_string", [],
            arrow_type string_t (opt_type isize_t));
           (Ast.VName "of_string_unsafe", [],
            arrow_type string_t isize_t);
           (Ast.VName "of_i8", [],
            arrow_type i8_t  isize_t);
           (Ast.VName "of_i16", [],
            arrow_type i16_t isize_t);
           (Ast.VName "of_i32", [],
            arrow_type i32_t isize_t);
           (Ast.VName "of_i64", [],
            arrow_type i64_t isize_t);
           (Ast.VName "of_u8", [],
            arrow_type u8_t isize_t);
           (Ast.VName "of_u16", [],
            arrow_type u16_t isize_t);
           (Ast.VName "of_u32", [],
            arrow_type u32_t isize_t);
           (Ast.VName "of_u64", [],
            arrow_type u64_t (opt_type isize_t));
           (Ast.VName "of_usize", [],
            arrow_type usize_t (opt_type isize_t));
           (Ast.VName "of_u64_wrapped", [],
            arrow_type u64_t isize_t);
           (Ast.VName "of_usize_wrapped", [],
            arrow_type usize_t isize_t);
         ];
      };
      {mod_name   = Ast.Mod_inferred "U64";
       mod_values = [
           (Ast.VName "of_byte", [],
            arrow_type byte_t u64_t);
           (Ast.VName "of_bytes", [],
            arrow_type (list_type byte_t) (opt_type u64_t));
           (Ast.VName "of_bytes_unsafe", [],
            arrow_type (list_type byte_t) u64_t);
           (Ast.VName "of_string", [],
            arrow_type string_t (opt_type u64_t));
           (Ast.VName "of_string_unsafe", [],
            arrow_type string_t u64_t);
           (Ast.VName "of_i8", [],
            arrow_type i8_t  (opt_type u64_t));
           (Ast.VName "of_i16", [],
            arrow_type i16_t (opt_type u64_t));
           (Ast.VName "of_i32", [],
            arrow_type i32_t (opt_type u64_t));
           (Ast.VName "of_i64", [],
            arrow_type i64_t (opt_type u64_t));
           (Ast.VName "of_isize", [],
            arrow_type isize_t (opt_type u64_t));
           (Ast.VName "of_u8", [],
            arrow_type u8_t  u64_t);
           (Ast.VName "of_u16", [],
            arrow_type u16_t u64_t);
           (Ast.VName "of_u32", [],
            arrow_type u32_t u64_t);
           (Ast.VName "of_usize", [],
            arrow_type usize_t (opt_type u64_t));
           (Ast.VName "of_i8_wrapped", [],
            arrow_type i8_t  u64_t);
           (Ast.VName "of_i16_wrapped", [],
            arrow_type i16_t u64_t);
           (Ast.VName "of_i32_wrapped", [],
            arrow_type i32_t u64_t);
           (Ast.VName "of_i64_wrapped", [],
            arrow_type i64_t u64_t);
           (Ast.VName "of_isize_wrapped", [],
            arrow_type isize_t u64_t);
           (Ast.VName "of_usize_wrapped", [],
            arrow_type usize_t u64_t);
         ];
      };
      {mod_name   = Ast.Mod_inferred "Usize";
       mod_values = [
           (Ast.VName "of_byte", [],
            arrow_type byte_t usize_t);
           (Ast.VName "of_bytes", [],
            arrow_type (list_type byte_t) (opt_type usize_t));
           (Ast.VName "of_bytes_unsafe", [],
            arrow_type (list_type byte_t) usize_t);
           (Ast.VName "of_string", [],
            arrow_type string_t (opt_type usize_t));
           (Ast.VName "of_string_unsafe", [],
            arrow_type string_t usize_t);
           (Ast.VName "of_i8", [],
            arrow_type i8_t  (opt_type usize_t));
           (Ast.VName "of_i16", [],
            arrow_type i16_t (opt_type usize_t));
           (Ast.VName "of_i32", [],
            arrow_type i32_t (opt_type usize_t));
           (Ast.VName "of_i64", [],
            arrow_type i64_t (opt_type usize_t));
           (Ast.VName "of_u8", [],
            arrow_type u8_t usize_t);
           (Ast.VName "of_u16", [],
            arrow_type u16_t usize_t);
           (Ast.VName "of_u32", [],
            arrow_type u32_t usize_t);
           (Ast.VName "of_u64", [],
            arrow_type u64_t usize_t);
           (Ast.VName "of_isize", [],
            arrow_type isize_t (opt_type usize_t));
           (Ast.VName "of_i8_wrapped", [],
            arrow_type i8_t  usize_t);
           (Ast.VName "of_i16_wrapped", [],
            arrow_type i16_t usize_t);
           (Ast.VName "of_i32_wrapped", [],
            arrow_type i32_t usize_t);
           (Ast.VName "of_i64_wrapped", [],
            arrow_type i64_t usize_t);
           (Ast.VName "of_isize_wrapped", [],
            arrow_type isize_t usize_t);
         ];
      };
      {mod_name   = Ast.Mod_inferred "Double";
       mod_values = [
           (Ast.VName "of_byte", [],
            arrow_type byte_t double_t);
           (Ast.VName "of_bytes", [],
            arrow_type (list_type byte_t) (opt_type double_t));
           (Ast.VName "of_bytes_unsafe", [],
            arrow_type (list_type byte_t) double_t);
           (Ast.VName "of_string", [],
            arrow_type string_t (opt_type double_t));
           (Ast.VName "of_string_unsafe", [],
            arrow_type string_t double_t);
         ];
      };
      {mod_name   = Ast.Mod_inferred "List";
       mod_values = [
           (Ast.VName "head", [ TName "a" ],
            arrow_type (list_type (gen_tvar "a"))
              (gen_tvar "a"));
           (Ast.VName "tail", [ TName "a" ],
            arrow_type (list_type (gen_tvar "a"))
              (list_type (gen_tvar "a")));
           (Ast.VName "index", [ TName "a" ],
            arrow_type (list_type (gen_tvar "a"))
              (arrow_type usize_t (opt_type (gen_tvar "a"))));
           (Ast.VName "index_unsafe", [ TName "a" ],
            arrow_type (list_type (gen_tvar "a"))
              (arrow_type usize_t (gen_tvar "a")));
           (Ast.VName "length", [ TName "a" ],
            arrow_type (list_type (gen_tvar "a")) usize_t);
           (Ast.VName "concat", [ TName "a" ],
            arrow_type (list_type (gen_tvar "a"))
              (arrow_type (list_type (gen_tvar "a"))
                 (list_type (gen_tvar "a"))));
           (Ast.VName "flatten", [ TName "a" ],
            arrow_type (list_type (list_type (gen_tvar "a")))
              (list_type (gen_tvar "a")));
           (Ast.VName "map", [ TName "a"; TName "b" ],
            arrow_type (arrow_type (gen_tvar "a") (gen_tvar "b"))
              (arrow_type (list_type (gen_tvar "a"))
                 (list_type (gen_tvar "b"))));
           (Ast.VName "fold", [ TName "a"; TName "b" ],
            arrow_type (arrow_type (gen_tvar "b")
                          (arrow_type (gen_tvar "a") (gen_tvar "b")))
              (arrow_type (list_type (gen_tvar "a")) (gen_tvar "b")));
           (Ast.VName "rev", [ TName "a" ],
            arrow_type (list_type (gen_tvar "a"))
              (list_type (gen_tvar "a")));
           (Ast.VName "map2", [ TName "a"; TName "b"; TName "c" ],
            arrow_type (arrow_type (gen_tvar "a")
                          (arrow_type (gen_tvar "b") (gen_tvar "c")))
              (arrow_type (list_type (gen_tvar "a"))
                 (arrow_type (list_type (gen_tvar "b"))
                    (list_type (gen_tvar "c")))));
           (Ast.VName "repl", [ TName "a" ],
            arrow_type (gen_tvar "a")
              (arrow_type usize_t (list_type (gen_tvar "a"))));
         ];
      };
      {mod_name   = Ast.Mod_inferred "String";
       mod_values = [
           (Ast.VName "empty", [], string_t);
           (Ast.VName "concat", [],
            arrow_type string_t (arrow_type string_t string_t));
           (Ast.VName "to_bytes", [],
            arrow_type string_t (list_type byte_t));
           (Ast.VName "of_bytes", [],
            arrow_type (list_type byte_t) (opt_type string_t));
           (Ast.VName "of_bytes_unsafe", [],
            arrow_type (list_type byte_t) string_t);
           (Ast.VName "of_literal", [],
            arrow_type (list_type byte_t) string_t)
         ];
      };
      {mod_name   = Ast.Mod_inferred "Bits";
       mod_values = [
           (* TODO: safe version of these conversions *)
           (Ast.VName "to_isize", [ TName "a" ],
            arrow_type (bitvector_type (gen_tvar "a")) isize_t);
           (Ast.VName "to_usize", [ TName "a" ],
            arrow_type (bitvector_type (gen_tvar "a")) usize_t);
           (Ast.VName "to_i8", [ TName "a" ],
            arrow_type (bitvector_type (gen_tvar "a")) i8_t);
           (Ast.VName "to_u8", [ TName "a" ],
            arrow_type (bitvector_type (gen_tvar "a")) u8_t);
           (Ast.VName "to_i16", [ TName "a" ],
            arrow_type (bitvector_type (gen_tvar "a")) i16_t);
           (Ast.VName "to_u16", [ TName "a" ],
            arrow_type (bitvector_type (gen_tvar "a")) u16_t);
           (Ast.VName "to_i32", [ TName "a" ],
            arrow_type (bitvector_type (gen_tvar "a")) i32_t);
           (Ast.VName "to_u32", [ TName "a" ],
            arrow_type (bitvector_type (gen_tvar "a")) u32_t);
           (Ast.VName "to_i64", [ TName "a" ],
            arrow_type (bitvector_type (gen_tvar "a")) i64_t);
           (Ast.VName "to_u64", [ TName "a" ],
            arrow_type (bitvector_type (gen_tvar "a")) u64_t);

           (* with endianness.  TODO: safe versions *)
           (Ast.VName "to_i16_endian", [ TName "a" ],
            arrow_type endian_t
              (arrow_type (bitvector_type (gen_tvar "a")) i16_t));
           (Ast.VName "to_u16_endian", [ TName "a" ],
            arrow_type endian_t
              (arrow_type (bitvector_type (gen_tvar "a")) u16_t));
           (Ast.VName "to_i32_endian", [ TName "a" ],
            arrow_type endian_t
              (arrow_type (bitvector_type (gen_tvar "a")) i32_t));
           (Ast.VName "to_u32_endian", [ TName "a" ],
            arrow_type endian_t
              (arrow_type (bitvector_type (gen_tvar "a")) u32_t));
           (Ast.VName "to_i64_endian", [ TName "a" ],
            arrow_type endian_t
              (arrow_type (bitvector_type (gen_tvar "a")) i64_t));
           (Ast.VName "to_u64_endian", [ TName "a" ],
            arrow_type endian_t
              (arrow_type (bitvector_type (gen_tvar "a")) u64_t));
           (Ast.VName "to_isize_endian", [ TName "a" ],
            arrow_type endian_t
              (arrow_type (bitvector_type (gen_tvar "a")) isize_t));
           (Ast.VName "to_usize_endian", [ TName "a" ],
            arrow_type endian_t
              (arrow_type (bitvector_type (gen_tvar "a")) usize_t));

           (Ast.VName "to_bool", [], arrow_type bit_t bool_t);
           (Ast.VName "of_bool", [], arrow_type bool_t bit_t);
           (Ast.VName "to_bit", [],
            arrow_type (bitvector_type (gen_tname "1")) bit_t);
           (Ast.VName "of_bit", [],
            arrow_type bit_t (bitvector_type (gen_tname "1")));
           (Ast.VName "ones", [ TName "a" ],
            arrow_type usize_t (bitvector_type (gen_tvar "a")));
           (Ast.VName "zeros", [ TName "a" ],
            arrow_type usize_t (bitvector_type (gen_tvar "a")));
         ];
      };
      {mod_name   = Ast.Mod_inferred "Set";
       mod_values = [
           (Ast.VName "empty", [ TName "a" ],
            (set_type (gen_tvar "a")));
           (Ast.VName "add", [ TName "a" ],
            arrow_type (set_type (gen_tvar "a"))
              (arrow_type (gen_tvar "a")
                 (set_type (gen_tvar "a"))));
           (Ast.VName "mem", [ TName "a" ],
            arrow_type (set_type (gen_tvar "a"))
              (arrow_type (gen_tvar "a") bool_t));
         ];
      };
      {mod_name   = Ast.Mod_inferred "Map";
       mod_values = [
           (Ast.VName "empty", [ TName "a"; TName "b" ],
            (map_type (gen_tvar "a") (gen_tvar "b")));
           (Ast.VName "add", [ TName "a"; TName "b" ],
            arrow_type (map_type (gen_tvar "a") (gen_tvar "b"))
              (arrow_type (gen_tvar "a")
                 (arrow_type (gen_tvar "b")
                    (map_type (gen_tvar "a") (gen_tvar "b")))));
           (Ast.VName "mem", [ TName "a" ; TName "b" ],
            arrow_type (map_type (gen_tvar "a") (gen_tvar "b"))
              (arrow_type (gen_tvar "a") bool_t));
           (Ast.VName "find", [ TName "a" ; TName "b" ],
            arrow_type (map_type (gen_tvar "a") (gen_tvar "b"))
              (arrow_type (gen_tvar "a") (opt_type (gen_tvar "b"))));
           (Ast.VName "find_unsafe", [ TName "a" ; TName "b" ],
            arrow_type (map_type (gen_tvar "a") (gen_tvar "b"))
              (arrow_type (gen_tvar "a") (gen_tvar "b")));
         ];
      };
      {mod_name   = Ast.Mod_inferred "View";
       mod_values = [
           (Ast.VName "get_current", [], (arrow_type unit_t view_t));
           (Ast.VName "get_base", [],  (arrow_type unit_t view_t));
           (Ast.VName "get_cursor", [], (arrow_type view_t usize_t));
           (Ast.VName "get_remaining", [], (arrow_type view_t usize_t));
           (Ast.VName "get_current_cursor", [], (arrow_type unit_t usize_t));
           (Ast.VName "get_current_remaining", [], (arrow_type unit_t usize_t));
           (Ast.VName "restrict", [],
            (arrow_type view_t (arrow_type usize_t (arrow_type usize_t view_t))));
           (Ast.VName "restrict_from", [],
            (arrow_type view_t (arrow_type usize_t view_t)));
           (Ast.VName "clone", [],
            (arrow_type view_t view_t));
         ];
      };
    ] in
  (* Builtin non-terminals are encoded as basic types. *)
  let builtin_non_terms : builtin_non_term array = [|
      (* atomic values *)
      NName "Byte",       [], byte_t;
      NName "AsciiChar",  [], byte_t;
      NName "HexChar",    [], byte_t;
      NName "AlphaNum",   [], byte_t;
      NName "Digit",      [], byte_t;
      (* composable with regular expressions *)
      NName "AsciiCharS", [], list_type byte_t;
      NName "HexCharS",   [], list_type byte_t;
      NName "AlphaNumS",  [], list_type byte_t;
      NName "DigitS",     [], list_type byte_t;
      (* binary integer types *)
      NName "Int8",   [], i8_t;
      NName "UInt8",  [], u8_t;
      NName "Int16",  [make_var "endian", endian_t, ()], i16_t;
      NName "UInt16", [make_var "endian", endian_t, ()], u16_t;
      NName "Int32",  [make_var "endian", endian_t, ()], i32_t;
      NName "UInt32", [make_var "endian", endian_t, ()], u32_t;
      NName "Int64",  [make_var "endian", endian_t, ()], i64_t;
      NName "UInt64", [make_var "endian", endian_t, ()], u64_t;
    |] in
  builtin_types, builtin_ops, builtin_values,
  builtin_modules, builtin_non_terms

module StringSet = Set.Make(String)

let std_types =
  StringSet.of_list (List.map (fun (Ast.TName t, _) -> t)
                       (Array.to_list builtin_types))
let is_builtin_type s = StringSet.mem s std_types

let std_values =
  StringSet.of_list (List.map (fun (Ast.VName v, _, _) -> v)
                       (Array.to_list builtin_values))
let is_builtin_value s = StringSet.mem s std_values

let std_nonterms =
  StringSet.of_list (List.map (fun (Ast.NName n, _, _) -> n)
                       (Array.to_list builtin_non_terms))
let is_builtin_nonterm s = StringSet.mem s std_nonterms

let std_modules =
  StringSet.of_list (List.map (fun ({mod_name = m; _}) ->
                                    match m with
                                      | Ast.Mod_inferred m -> m
                                      | _ -> assert false)
                       builtin_modules)
let is_builtin_module s = StringSet.mem s std_modules

(* future-proofing *)

let std_fields = StringSet.empty
let is_builtin_field f = StringSet.mem f std_fields

(* module members that are higher-order *)
module ModuleMembers = Set.Make(struct type t = string * string
                                       let compare = compare
                                end)
let higher_order =
  ModuleMembers.of_list [
      ("List", "map");
      ("List", "map2");
      ("List", "fold");
      (* add similar functions for Set and Map *)
    ]
let is_higher_order (m, i) =
  let mm = Location.value m, Location.value i in
  ModuleMembers.mem mm higher_order

(* Types that are character classes and their membership *)

let character_classes =
  let ascii =
    Array.init 255 (fun i -> Char.chr i) in
  let hex =
    Array.of_list ['0';'1';'2';'3';'4';'5';'6';'7';'8';'9';
                   'a';'b';'c';'d';'e';'f';
                   'A';'B';'C';'D';'E';'F'] in
  let digits =
    Array.of_list ['0';'1';'2';'3';'4';'5';'6';'7';'8';'9'] in
  let lower =
    Array.init 26 (fun i -> Char.chr (i + 97)) in
  let upper =
    Array.init 26 (fun i -> Char.chr (i + 65)) in
  let alphanum =
    Array.of_list (Array.to_list digits
                   @ Array.to_list lower
                   @ Array.to_list upper) in
  [ "AsciiCharS", ascii;
    "HexCharS",   hex;
    "AlphaNumS",  alphanum;
    "DigitS",     digits;
  ]

let is_character_class t =
  List.mem (Location.value t) (List.map fst character_classes)

let mk_builtin_bitwidth i =
  assert(i >= 0);
  let n = string_of_int i in
  let syn = (false, Assoc_none, 1) in
  Ast.TName n, (Ast.KNat, syn, [])

(* helpers for printing *)

let as_symbol name =
  match name with
    | m, name when m = AstUtils.stdlib ->
        Misc.array_associ_opt name builtin_types
    | _ ->
        None

let infix, priority, associativity =
  let is_builtin op =
    0 <= op && op < Array.length builtin_types in
  let get_syntax (_, s, _) = s in
  let get_infix t =
    let (i, _, _) = get_syntax t in
    i in
  let get_assoc t =
    let (_, a, _) = get_syntax t in
    a in
  let get_priority t =
    let (_, _, p) = get_syntax t in
    p in

  let infix op =
    if is_builtin op
    then get_infix (snd builtin_types.(op))
    else false in
  let priority op =
    if is_builtin op
    then get_priority (snd builtin_types.(op))
    else max_int in
  let associativity op =
    if is_builtin op
    then get_assoc (snd builtin_types.(op))
    else Assoc_none in
  infix, priority, associativity

(** These names are used in the constraints and need to correspond to
    the type::constructor encoding of the builtin definitions. *)

(* use internal naming of width for operators *)
let str_of_width = function
  | Ast.NW_size -> ""
  | Ast.NW_8    -> "8"
  | Ast.NW_16   -> "16"
  | Ast.NW_32   -> "32"
  | Ast.NW_64   -> "64"

let str_of_num (s, w) =
  Ast.str_of_signed s ^ str_of_width w

let unop_const_name = function
  | Ast.Uminus n -> "1-_" ^ str_of_num n
  | Ast.Inot n   -> "~_"  ^ str_of_num n
  | Ast.Not      -> "!"
  | Ast.Neg_b    -> "~"

let binop_const_name = function
  | Ast.Plus n  -> "+_"  ^ str_of_num n
  | Ast.Minus n -> "-_"  ^ str_of_num n
  | Ast.Mult n  -> "*_"  ^ str_of_num n
  | Ast.Mod n   -> "%_"  ^ str_of_num n
  | Ast.Div n   -> "/_"  ^ str_of_num n
  | Ast.Lt n    -> "<_"  ^ str_of_num n
  | Ast.Gt n    -> ">_"  ^ str_of_num n
  | Ast.Lteq n  -> "<=_" ^ str_of_num n
  | Ast.Gteq n  -> ">=_" ^ str_of_num n

  | Ast.Iand n  -> "&_"   ^ str_of_num n
  | Ast.Ior n   -> "|_"   ^ str_of_num n
  | Ast.Ixor n  -> "^_"   ^ str_of_num n
  | Ast.Lshft n -> "<<_"  ^ str_of_num n
  | Ast.Rshft n -> ">>_"  ^ str_of_num n
  | Ast.Ashft n -> ">>_a" ^ str_of_num n

  | Ast.Or_b    -> "|_b"
  | Ast.And_b   -> "&_b"
  | Ast.Land    -> "&&"
  | Ast.Lor     -> "||"

  | Ast.Eq      -> "="
  | Ast.Neq     -> "!="

  | Ast.Index   -> ".[]"

  (* data constructors *)
  | Ast.Cons    -> "[]::::"
  (* functions *)
  | Ast.Plus_s  -> "String.concat"
  | Ast.At      -> "List.concat"

type 'a environment = Ast.full_tname -> 'a arterm

(* Wrap a type identifier into the stdlib module,
   which is included by default and hence has a `None` specifier. *)
let mk_stdlib_t t =
  AstUtils.stdlib, (Ast.TName t)

let symbol tenv (i : Ast.full_tname) =
  tenv i

let option tenv t =
  let v = symbol tenv (mk_stdlib_t "option") in
  TTerm (App (v, t))

let list tenv t =
  let v = symbol tenv (mk_stdlib_t "[]") in
  TTerm (App (v, t))

let arrow tenv t u =
  let v = symbol tenv (mk_stdlib_t "->") in
  TTerm (App (TTerm (App (v, t)), u))

let n_arrows tenv ts u =
  List.fold_left (fun acu x -> arrow tenv acu x) u ts

let tuple tenv ps =
  let n = if ps = [] then "unit" else "*" in
  let v = symbol tenv (mk_stdlib_t n) in
  List.fold_left (fun acu x -> TTerm (App (acu, x))) v ps

let concrete_bitvector tenv n =
  let t = symbol tenv (mk_stdlib_t "bitvector") in
  let n = symbol tenv (mk_stdlib_t (string_of_int n)) in
  TTerm (App (t, n))

let abstract_bitvector tenv t =
  let b = symbol tenv (mk_stdlib_t "bitvector") in
  TTerm (App (b, t))

let is_regexp_type tenv t =
  let c = symbol tenv (mk_stdlib_t "[]") in
  match t with
    | TTerm (App (v, t)) when v = c ->
        let b = symbol tenv (mk_stdlib_t "byte") in
        t = b
    | _ -> false

let type_of_primitive tenv = function
  | Ast.PL_int (_, n)   -> symbol tenv (mk_stdlib_t (Ast.str_of_num_t n))
  | Ast.PL_bytes _      -> list tenv (symbol tenv (mk_stdlib_t "byte"))
  | Ast.PL_unit         -> symbol tenv (mk_stdlib_t "unit")
  | Ast.PL_bool _       -> symbol tenv (mk_stdlib_t "bool")
  | Ast.PL_bit _        -> symbol tenv (mk_stdlib_t "bit")
  | Ast.PL_bitvector bv -> concrete_bitvector tenv (List.length bv)

let result_type tenv t =
  let a = symbol tenv (mk_stdlib_t "->") in
  let rec chop t =
    match t with
      | TTerm (App (TTerm (App (v, _)), u)) when v = a -> chop u
      | u -> u
  in
    chop t

let arg_types tenv t =
  let a = symbol tenv (mk_stdlib_t "->") in
  let rec chop acu = function
    | TTerm (App (TTerm (App (v, t)), u)) when v = a -> chop (t :: acu) u
    | _ -> acu
  in
    List.rev (chop [] t)

let tycon_args t =
  let rec chop acu = function
    | TTerm (App (t, u)) -> chop (u :: acu) t
    | _ -> acu
  in
    chop [] t

let rec tycon_name = function
  | TTerm (App (u, _)) -> tycon_name u
  | TVariable _ as t -> t
  | _ -> assert false
