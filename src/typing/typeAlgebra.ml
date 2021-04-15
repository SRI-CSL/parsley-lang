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
open MultiEquation
open CoreAlgebra

type builtin_dataconstructor =
  Ast.dname * Ast.tname list * Ast.type_expr

type builtin_type =
  Ast.tname * (Ast.kind * builtin_dataconstructor list)

type builtin_non_term =
  Ast.nname * (unit Ast.var * Ast.type_expr) list * Ast.type_expr

type builtin_module =
  {mod_name:   Ast.mname;
   mod_values: builtin_dataconstructor list}

let builtin_types, builtin_consts, builtin_vars,
    builtin_modules, builtin_non_terms =
  let ghost_loc = Location.ghost_loc in
  let make_var (s: string) =
    Location.mk_ghost (s, ()) in
  let make_builtin_type (t : Ast.type_expr_desc) =
    {Ast.type_expr = t;
     Ast.type_expr_loc = ghost_loc} in
  let arrow_type t1 t2 : Ast.type_expr =
    let tvar = Location.mk_loc_val "->" ghost_loc in
    let con = make_builtin_type (Ast.TE_tvar tvar) in
    make_builtin_type (Ast.TE_tapp (con, [ t1; t2 ])) in
  let tuple_type t1 t2 : Ast.type_expr =
    let tvar = Location.mk_loc_val "*" ghost_loc in
    let con = make_builtin_type (Ast.TE_tvar tvar) in
    make_builtin_type (Ast.TE_tapp (con, [ t1; t2 ])) in
  let list_type t : Ast.type_expr =
    let tvar = Location.mk_loc_val "[]" ghost_loc in
    let con = make_builtin_type (Ast.TE_tvar tvar) in
    make_builtin_type (Ast.TE_tapp (con, [ t ])) in
  let opt_type t : Ast.type_expr =
    let tvar  = Location.mk_loc_val "option" ghost_loc in
    let con = make_builtin_type (Ast.TE_tvar tvar) in
    make_builtin_type (Ast.TE_tapp (con, [ t ])) in
  let set_type t : Ast.type_expr =
    let tvar  = Location.mk_loc_val "set" ghost_loc in
    let con = make_builtin_type (Ast.TE_tvar tvar) in
    make_builtin_type (Ast.TE_tapp (con, [ t ])) in
  let map_type k v : Ast.type_expr =
    let tvar  = Location.mk_loc_val "map" ghost_loc in
    let con = make_builtin_type (Ast.TE_tvar tvar) in
    make_builtin_type (Ast.TE_tapp (con, [ k; v ])) in
  let gen_tvar (v : string) : Ast.type_expr =
    let tvar = Location.mk_loc_val v ghost_loc in
    make_builtin_type (Ast.TE_tvar tvar) in
  let builtin_types : builtin_type array = [|
      TName "->",     (Ast.KArrow (Ast.KStar, Ast.KArrow (Ast.KStar, Ast.KStar)), []);
      TName "*",      (Ast.KArrow (Ast.KStar, Ast.KArrow (Ast.KStar, Ast.KStar)),
                       [ (Ast.DName "_Tuple", [ TName "a"; TName "b" ],
                          arrow_type (gen_tvar "a")
                            (arrow_type (gen_tvar "b")
                               (tuple_type (gen_tvar "a")
                                  (gen_tvar "b")))) ]);

      TName "[]",     (Ast.KArrow (Ast.KStar, Ast.KStar),
                       [ (Ast.DName "::", [ TName "a" ],
                          arrow_type (gen_tvar "a")
                            (arrow_type (list_type (gen_tvar "a"))
                               (list_type (gen_tvar "a"))));
                         (Ast.DName "[]", [ TName "a" ],
                          list_type (gen_tvar "a")) ]);
      TName "option", (Ast.KArrow (Ast.KStar, Ast.KStar),
                       [ (Ast.DName "None", [ TName "a" ],
                          opt_type (gen_tvar "a"));
                         (Ast.DName "Some", [ TName "a" ],
                          arrow_type (gen_tvar "a")
                            (opt_type (gen_tvar "a"))) ]);

      TName "int",    (Ast.KStar, []);
      TName "double", (Ast.KStar, []);
      TName "char",   (Ast.KStar, []);
      TName "byte",   (Ast.KStar, []);
      TName "string", (Ast.KStar, []);
      TName "unit",   (Ast.KStar,
                       [ (Ast.DName "_Unit", [], gen_tvar "unit") ]);
      TName "bool",   (Ast.KStar,
                       [ (Ast.DName "True", [], gen_tvar "bool");
                         (Ast.DName "False", [], gen_tvar "bool") ]);
      TName "endian", (Ast.KStar,
                       [ (Ast.DName "Big", [], gen_tvar "endian");
                         (Ast.DName "Little", [], gen_tvar "endian") ]);
      TName "bit",    (Ast.KStar,
                       [ (Ast.DName "One",  [], gen_tvar "bit");
                         (Ast.DName "Zero", [], gen_tvar "bit") ]);
      TName "bitvector", (Ast.KArrow (Ast.KNat, Ast.KStar), []);
      (* module types *)
      TName "view",   (Ast.KStar, []);
      TName "set",    ((Ast.KArrow (Ast.KStar, Ast.KStar)), []);
      TName "map",    ((Ast.KArrow
                          (Ast.KStar,
                           (Ast.KArrow (Ast.KStar, Ast.KStar)))),
                       []);
    |] in
  let builtin_consts : builtin_dataconstructor array = [|
      (Ast.DName "1-", [], arrow_type (gen_tvar "int") (gen_tvar "int"));
      (Ast.DName "!",  [], arrow_type (gen_tvar "bool") (gen_tvar "bool"));

      (Ast.DName "+",  [], arrow_type (gen_tvar "int")
                             (arrow_type (gen_tvar "int") (gen_tvar "int")));
      (Ast.DName "-",  [], arrow_type (gen_tvar "int")
                             (arrow_type (gen_tvar "int") (gen_tvar "int")));
      (Ast.DName "*",  [], arrow_type (gen_tvar "int")
                             (arrow_type (gen_tvar "int") (gen_tvar "int")));
      (Ast.DName "/",  [], arrow_type (gen_tvar "int")
                             (arrow_type (gen_tvar "int") (gen_tvar "int")));

      (Ast.DName "<",  [], arrow_type (gen_tvar "int")
                             (arrow_type (gen_tvar "int") (gen_tvar "bool")));
      (Ast.DName ">",  [], arrow_type (gen_tvar "int")
                             (arrow_type (gen_tvar "int") (gen_tvar "bool")));
      (Ast.DName "<=", [], arrow_type (gen_tvar "int")
                             (arrow_type (gen_tvar "int") (gen_tvar "bool")));
      (Ast.DName ">=", [], arrow_type (gen_tvar "int")
                             (arrow_type (gen_tvar "int") (gen_tvar "bool")));

      (Ast.DName "&&", [], arrow_type (gen_tvar "bool")
                             (arrow_type (gen_tvar "bool") (gen_tvar "bool")));
      (Ast.DName "||", [], arrow_type (gen_tvar "bool")
                             (arrow_type (gen_tvar "bool") (gen_tvar "bool")));

      (Ast.DName "=",  [ TName "a" ], arrow_type (gen_tvar "a")
                                        (arrow_type (gen_tvar "a")
                                           (gen_tvar "bool")));
      (Ast.DName "!=", [ TName "a" ], arrow_type (gen_tvar "a")
                                        (arrow_type (gen_tvar "a")
                                           (gen_tvar "bool")));
      (Ast.DName "!=", [ TName "a" ], arrow_type (gen_tvar "a")
                                        (arrow_type (gen_tvar "a")
                                           (gen_tvar "bool")));

      (Ast.DName ".[]", [ TName "a" ], arrow_type (list_type (gen_tvar "a"))
                                        (arrow_type (gen_tvar "int")
                                           (gen_tvar "a")));
    |] in
  let builtin_vars : builtin_dataconstructor array = [|
      (* utility convertors *)
      (Ast.DName "byte_of_int_unsafe", [], arrow_type (gen_tvar "int")
                                             (gen_tvar "byte"));
    |] in
  let builtin_modules : builtin_module list = [
      {mod_name   = Ast.MName "Int";
       mod_values = [
           (Ast.DName "of_byte", [],
            arrow_type (gen_tvar "byte")
              (gen_tvar "int"));
           (Ast.DName "of_string", [],
            arrow_type (gen_tvar "string")
              (opt_type (gen_tvar "int")));
           (Ast.DName "of_bytes", [],
            arrow_type (list_type (gen_tvar "byte"))
              (opt_type (gen_tvar "int")));
           (Ast.DName "of_bytes_unsafe", [],
            arrow_type (list_type (gen_tvar "byte"))
              (gen_tvar "int"));
         ];
      };
      {mod_name   = Ast.MName "Double";
       mod_values = [
           (Ast.DName "of_byte", [],
            arrow_type (gen_tvar "byte")
              (gen_tvar "double"));
           (Ast.DName "of_string", [],
            arrow_type (gen_tvar "string")
              (opt_type (gen_tvar "double")));
           (Ast.DName "of_bytes", [],
            arrow_type (list_type (gen_tvar "byte"))
              (opt_type (gen_tvar "double")));
           (Ast.DName "of_bytes_unsafe", [],
            arrow_type (list_type (gen_tvar "byte"))
              (gen_tvar "double"));
         ];
      };
      {mod_name   = Ast.MName "List";
       mod_values = [
           (Ast.DName "length", [ TName "a" ],
            arrow_type (list_type (gen_tvar "a"))
              (gen_tvar "int"));
           (Ast.DName "concat", [ TName "a" ],
            arrow_type (list_type (gen_tvar "a"))
              (arrow_type (list_type (gen_tvar "a"))
                 (list_type (gen_tvar "a"))));
           (Ast.DName "flatten", [ TName "a" ],
            arrow_type (list_type (list_type (gen_tvar "a")))
              (list_type (gen_tvar "a")));
           (Ast.DName "map", [ TName "a"; TName "b" ],
            arrow_type (arrow_type (gen_tvar "a") (gen_tvar "b"))
              (arrow_type (list_type (gen_tvar "a"))
                 (list_type (gen_tvar "b"))));
           (Ast.DName "rev", [ TName "a" ],
            arrow_type (list_type (gen_tvar "a"))
              (list_type (gen_tvar "a")));
           (Ast.DName "map2", [ TName "a"; TName "b"; TName "c" ],
            arrow_type (arrow_type (gen_tvar "a")
                          (arrow_type (gen_tvar "b") (gen_tvar "c")))
              (arrow_type (list_type (gen_tvar "a"))
                 (arrow_type (list_type (gen_tvar "b"))
                    (list_type (gen_tvar "c")))));
           (Ast.DName "repl", [ TName "a" ],
            arrow_type (gen_tvar "a")
              (arrow_type (gen_tvar "int") (list_type (gen_tvar "a"))));
         ];
      };
      {mod_name   = Ast.MName "Set";
       mod_values = [
           (Ast.DName "empty", [ TName "a" ],
            (set_type (gen_tvar "a")));
           (Ast.DName "add", [ TName "a" ],
            arrow_type (set_type (gen_tvar "a"))
              (arrow_type (gen_tvar "a")
                 (set_type (gen_tvar "a"))));
           (Ast.DName "mem", [ TName "a" ],
            arrow_type (set_type (gen_tvar "a"))
              (arrow_type (gen_tvar "a")
                 (gen_tvar "bool")));
         ];
      };
      {mod_name   = Ast.MName "Map";
       mod_values = [
           (Ast.DName "empty", [ TName "a"; TName "b" ],
            (map_type (gen_tvar "a") (gen_tvar "b")));
           (Ast.DName "add", [ TName "a"; TName "b" ],
            arrow_type (map_type (gen_tvar "a") (gen_tvar "b"))
              (arrow_type (gen_tvar "a")
                 (arrow_type (gen_tvar "b")
                    (map_type (gen_tvar "a") (gen_tvar "b")))));
           (Ast.DName "mem", [ TName "a" ; TName "b" ],
            arrow_type (map_type (gen_tvar "a") (gen_tvar "b"))
              (arrow_type (gen_tvar "a")
                 (gen_tvar "bool")));
           (Ast.DName "find", [ TName "a" ; TName "b" ],
            arrow_type (map_type (gen_tvar "a") (gen_tvar "b"))
              (arrow_type (gen_tvar "a")
                 (opt_type (gen_tvar "b"))));
           (Ast.DName "find_unsafe", [ TName "a" ; TName "b" ],
            arrow_type (map_type (gen_tvar "a") (gen_tvar "b"))
              (arrow_type (gen_tvar "a") (gen_tvar "b")));
         ];
      };
      {mod_name   = Ast.MName "String";
       mod_values = [
           (Ast.DName "empty", [], gen_tvar "string");
           (Ast.DName "concat", [],
            arrow_type (gen_tvar "string")
              (arrow_type (gen_tvar "string")
                 (gen_tvar "string")));
           (Ast.DName "to_int", [],
            arrow_type (gen_tvar "string")
              (opt_type (gen_tvar "int")));
           (Ast.DName "to_bytes", [],
            arrow_type (gen_tvar "string")
              (list_type (gen_tvar "byte")));
           (Ast.DName "of_bytes", [],
            arrow_type (list_type (gen_tvar "byte"))
              (opt_type (gen_tvar "string")));
           (Ast.DName "of_bytes_unsafe", [],
            arrow_type (list_type (gen_tvar "byte"))
              (gen_tvar "string"));
         ];
      };
      {mod_name   = Ast.MName "View";
       mod_values = [
           (Ast.DName "get_base", [],
            (arrow_type (gen_tvar "unit")
               (gen_tvar "view")));
           (Ast.DName "get_current", [],
            (arrow_type (gen_tvar "unit")
               (gen_tvar "view")));
           (Ast.DName "get_current_cursor", [],
            (arrow_type (gen_tvar "unit")
               (gen_tvar "int")));
           (Ast.DName "make_current", [],
            (arrow_type (gen_tvar "view")
               (gen_tvar "unit")));
           (Ast.DName "restrict", [],
            (arrow_type (gen_tvar "view")
               (arrow_type (gen_tvar "int")
                  (arrow_type (gen_tvar "int")
                     (gen_tvar "view")))));
           (Ast.DName "restrict_from", [],
            (arrow_type (gen_tvar "view")
               (arrow_type (gen_tvar "int")
                  (gen_tvar "view"))));
           (Ast.DName "clone", [],
            (arrow_type (gen_tvar "view")
               (gen_tvar "view")));
         ];
      };
    ] in
  (* Builtin non-terminals are encoded as basic types. *)
  let builtin_non_terms : builtin_non_term array = [|
      (* atomic values *)
      NName "Byte",       [], gen_tvar "byte";
      NName "AsciiChar",  [], gen_tvar "byte";
      NName "HexChar",    [], gen_tvar "byte";
      NName "AlphaNum",   [], gen_tvar "byte";
      NName "Digit",      [], gen_tvar "byte";
      (* composable with regular expressions *)
      NName "AsciiCharS", [], list_type (gen_tvar "byte");
      NName "HexCharS",   [], list_type (gen_tvar "byte");
      NName "AlphaNumS",  [], list_type (gen_tvar "byte");
      NName "DigitS",     [], list_type (gen_tvar "byte");
      (* binary integer types *)
      NName "Int8",   [], gen_tvar "int";
      NName "UInt8",  [], gen_tvar "int";
      NName "Int16",  [make_var "endian", gen_tvar "endian"], gen_tvar "int";
      NName "UInt16", [make_var "endian", gen_tvar "endian"], gen_tvar "int";
      NName "Int32",  [make_var "endian", gen_tvar "endian"], gen_tvar "int";
      NName "UInt32", [make_var "endian", gen_tvar "endian"], gen_tvar "int";
      NName "Int64",  [make_var "endian", gen_tvar "endian"], gen_tvar "int";
      NName "UInt64", [make_var "endian", gen_tvar "endian"], gen_tvar "int";
    |] in
  builtin_types, builtin_consts, builtin_vars,
  builtin_modules, builtin_non_terms

let mk_builtin_bitwidth i =
  assert(i >= 0);
  let n = string_of_int i in
  Ast.TName n, (Ast.KNat, [])

type symbol = int

let as_symbol name =
  Misc.just_try (fun () -> Misc.array_associ name builtin_types)

(** These names are used in the constraints and need to correspond to
    the type::constructor encoding of the builtin definitions. *)
let unop_const_name = function
  | Ast.Uminus -> "1-"
  | Ast.Not    -> "!"

let binop_const_name = function
  | Ast.Plus  -> "+"
  | Ast.Minus -> "-"
  | Ast.Mult  -> "*"
  | Ast.Div   -> "/"
  | Ast.Lt    -> "<"
  | Ast.Gt    -> ">"
  | Ast.Lteq  -> "<="
  | Ast.Gteq  -> ">="
  | Ast.Land  -> "&&"
  | Ast.Lor   -> "||"
  | Ast.Eq    -> "="
  | Ast.Neq   -> "!="
  | Ast.Index -> ".[]"
  (* data constructors *)
  | Ast.Cons  -> "[]::::"
  (* functions *)
  | Ast.Plus_s -> "String.concat"
  | Ast.At     -> "List.concat"

type 'a environment = tname -> 'a arterm

let symbol tenv (i : Ast.tname) =
  tenv i

let option tenv t =
  let v = symbol tenv (TName "option") in
  TTerm (App (v, t))

let list tenv t =
  let v = symbol tenv (TName "[]") in
  TTerm (App (v, t))

let arrow tenv t u =
  let v = symbol tenv (TName "->") in
  TTerm (App (TTerm (App (v, t)), u))

let n_arrows tenv ts u =
  List.fold_left (fun acu x -> arrow tenv acu x) u ts

let tuple tenv ps =
  let n = if ps = [] then "unit" else "*" in
  let v = symbol tenv (TName n) in
  List.fold_left (fun acu x -> TTerm (App (acu, x))) v ps

let concrete_bitvector tenv n =
  let t = symbol tenv (TName "bitvector") in
  let n = symbol tenv (TName (string_of_int n)) in
  TTerm (App (t, n))

let abstract_bitvector tenv t =
  let b = symbol tenv (TName "bitvector") in
  TTerm (App (b, t))

let is_regexp_type tenv t =
  let c = symbol tenv (TName "[]") in
  match t with
    | TTerm (App (v, t)) when v = c ->
        let b = symbol tenv (TName "byte") in
        t = b
    | _ -> false

let type_of_primitive tenv = function
  | Ast.PL_int _ -> symbol tenv (TName "int")
  | Ast.PL_string _ -> list tenv (symbol tenv (TName "byte"))
  | Ast.PL_unit -> symbol tenv (TName "unit")
  | Ast.PL_bool _ -> symbol tenv (TName "bool")
  | Ast.PL_bit _ -> symbol tenv (TName "bit")
  | Ast.PL_bitvector bv -> concrete_bitvector tenv (List.length bv)

let result_type tenv t =
  let a = symbol tenv (TName "->") in
  let rec chop t =
    match t with
      | TTerm (App (TTerm (App (v, _)), u)) when v = a -> chop u
      | u -> u
  in
    chop t

let arg_types tenv t =
  let a = symbol tenv (TName "->") in
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
