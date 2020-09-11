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
(*  Copyright (C) 2006. Fran�ois Pottier, Yann R�gis-Gianas               *)
(*  and Didier R�my.                                                      *)

open MultiEquation
open CoreAlgebra

type builtin_dataconstructor = Ast.dname * Ast.tname list * Ast.type_expr

let builtin_env =
  let ghost_loc = Location.ghost_loc in
  let make_builtin_type (t : Ast.type_expr_desc) =
    { Ast.type_expr = t;
      Ast.type_expr_loc = ghost_loc } in
  let arrow_type t1 t2 : Ast.type_expr =
    let tvar = Location.mk_loc_val "->" ghost_loc in
    let con = make_builtin_type (Ast.TE_tvar tvar) in
    make_builtin_type (Ast.TE_tapp (con, [ t1; t2 ])) in
  let tuple_type2 t1 t2 : Ast.type_expr =
    let tvar = Location.mk_loc_val "*" ghost_loc in
    let con = make_builtin_type (Ast.TE_tvar tvar) in
    make_builtin_type (Ast.TE_tapp (con, [ t1; t2 ])) in
  let gen_tvar (v : string) : Ast.type_expr =
    let tvar = Location.mk_loc_val v ghost_loc in
    make_builtin_type (Ast.TE_tvar tvar) in
  [|
    TName "->",     (Ast.KArrow (Ast.KStar, Ast.KArrow (Ast.KStar, Ast.KStar)), []);
    TName "*",      (Ast.KArrow (Ast.KStar, Ast.KArrow (Ast.KStar, Ast.KStar)),
                         [ (Ast.DName "_Tuple", [ TName "a"; TName "b" ],
                            arrow_type (gen_tvar "a")
                              (arrow_type (gen_tvar "b")
                                 (tuple_type2 (gen_tvar "a") (gen_tvar "b"))))
                         ]);

    TName "int",    (Ast.KStar, []);
    TName "char",   (Ast.KStar, []);
    TName "string", (Ast.KStar, []);
    TName "unit",   (Ast.KStar,
                     [ (Ast.DName "_Unit", [], gen_tvar "unit") ]);
    TName "bool",   (Ast.KStar,
                     [ (Ast.DName "true", [], gen_tvar "bool");
                       (Ast.DName "false", [], gen_tvar "bool") ]);
  |]

let init_builtin_env mk_variable =
  Array.fold_left
    (fun acu (o, (arity, ds)) ->
       (o, (arity,
            TVariable (mk_variable ?name:(Some o) ()),
            ds
           )
       ) :: acu)
    [] builtin_env

type 'a environment = tname -> 'a arterm

let symbol tenv (i : Ast.tname) =
  tenv i

let type_of_primitive tenv = function
  | Ast.PL_int _ -> symbol tenv (TName "int")
  | Ast.PL_string _ -> symbol tenv (TName "string")
  | Ast.PL_unit -> symbol tenv (TName "unit")
  | Ast.PL_bool _ -> symbol tenv (TName "bool")

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
