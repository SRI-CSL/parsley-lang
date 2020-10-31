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

open MultiEquation
open CoreAlgebra

type builtin_dataconstructor = Ast.dname * Ast.tname list * Ast.type_expr

let builtin_types, builtin_consts =
  let ghost_loc = Location.ghost_loc in
  let make_builtin_type (t : Ast.type_expr_desc) =
    { Ast.type_expr = t;
      Ast.type_expr_loc = ghost_loc } in
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
  let gen_tvar (v : string) : Ast.type_expr =
    let tvar = Location.mk_loc_val v ghost_loc in
    make_builtin_type (Ast.TE_tvar tvar) in
  let builtin_types = [|
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
      TName "char",   (Ast.KStar, []);
      TName "byte",   (Ast.KStar, []);
      TName "string", (Ast.KStar, []);
      TName "unit",   (Ast.KStar,
                       [ (Ast.DName "_Unit", [], gen_tvar "unit") ]);
      TName "bool",   (Ast.KStar,
                       [ (Ast.DName "True", [], gen_tvar "bool");
                         (Ast.DName "False", [], gen_tvar "bool") ])
    |] in
  let builtin_consts = [|
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
  builtin_types, builtin_consts

let init_builtin_types mk_variable =
  Array.fold_left
    (fun acu (o, (arity, ds)) ->
      (o, (arity,
           TVariable (mk_variable ?name:(Some o) ()),
           ds
          )
      ) :: acu)
    [] builtin_types

type symbol = int

let as_symbol name =
  Misc.just_try (fun () -> Misc.array_associ name builtin_types)

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
  | Ast.Cons  -> "::"
  | Ast.Index -> ".[]"

type 'a environment = tname -> 'a arterm

let symbol tenv (i : Ast.tname) =
  tenv i

let type_of_primitive tenv = function
  | Ast.PL_int _ -> symbol tenv (TName "int")
  | Ast.PL_string _ -> symbol tenv (TName "string")
  | Ast.PL_unit -> symbol tenv (TName "unit")
  | Ast.PL_bool _ -> symbol tenv (TName "bool")

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

let result_type tenv t =
  let a = symbol tenv (TName "->") in
  let rec chop t =
    match t with
      | TTerm (App (TTerm (App (v, t)), u)) when v = a -> chop u
      | u -> u
  in
    chop t

let arg_types tenv t =
  let a = symbol tenv (TName "->") in
  let rec chop acu = function
    | TTerm (App (TTerm (App (v, t)), u)) when v = a -> chop (t :: acu) u
    | x -> acu
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
  | TVariable v as t -> t
  | _ -> assert false
