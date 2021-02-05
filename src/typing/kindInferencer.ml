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

(** This module implements a simple kind inferencer. *)

open Parsing
open Ast
open MultiEquation
open TypingExceptions
open Misc

type variable =
  descriptor UnionFind.point

and descriptor =
  {mutable structure : term option;
   mutable name      : tname;
   mutable constant  : bool}

and term =
  | App of variable * variable

type t = variable

type env = (tname -> Location.t -> t) * (tname -> t -> unit)

let count = ref 0

let new_name () =
  incr count;
  TName ("V" ^ string_of_int !count)

let variable ?(name : tname option) () =
  let constant = (name <> None)
  and name = match name with None -> new_name () | Some n -> n in
  UnionFind.fresh {structure = None; name = name; constant = constant}

let structure v =
  (UnionFind.find v).structure

let iter_term f = function
  | App (t1, t2) ->
      f t1;
      f t2

let iter f v = iter_term f (unSome (structure v))

let lookup id loc tenv = (fst tenv) id loc

let term_handler t =
  UnionFind.fresh
    {name = TName "";
     structure = Some t;
     constant = false}

let binop op x y =
  let w = term_handler (App (op, x)) in
  term_handler (App (w, y))

let star =
  variable ~name:(TName "@") ()

let arrow =
  variable ~name:(TName "=>") ()

let mkarrow =
  binop arrow

let fresh_kind () =
  variable ()

let rec print_term = function
  | App (v1, v2) -> String.concat "" [ "(" ; print v1 ; "," ; print v2 ; ")" ]

and print v =
  match (UnionFind.find v).structure with
    | None -> name v
    | Some t -> print_term t

and name v =
  match (UnionFind.find v).name with
    | TName name -> name

let is_constant v = (UnionFind.find v).constant

let assign_point k1 k2 =
  let name, has_name =
    if is_constant k1 then name k1, true
    else if is_constant k2 then name k2, true
    else "", false
  in
    UnionFind.union k1 k2;
    if has_name then (
      (UnionFind.find k2).name <- TName name;
      (UnionFind.find k2).constant <- true
    )

let assign pos k1 k2 =
  iter (fun k -> if UnionFind.equivalent k1 k then raise (Error (KindError pos))) k2;
  assign_point k1 k2

let occur_check v1 v2 =
  let rec variables acu v =
    match (structure v) with
      | None -> if not (List.memq v acu) then v::acu else acu
      | Some (App (v1, v2)) -> variables (variables acu v1) v2 in
  let vars1 = variables [] v1
  and vars2 = variables [] v2 in
  List.memq v1 vars2 || List.memq v2 vars1

let rec unify pos k1 k2 =
(*  Printf.eprintf "%s =?= %s\n" (print k1) (print k2); *)
  if not (UnionFind.equivalent k1 k2) then (
    if occur_check k1 k2 then
      raise (Error (KindError pos));

    match structure k1, structure k2 with

      | None, None ->
          if (is_constant k1 && is_constant k2 && name k1 <> name k2) then
            raise (Error (KindError pos));
          assign_point k1 k2

      | (None, _ | _, None) when is_constant k1 || is_constant k2 ->
          raise (Error (KindError pos))

      | None, _ ->
          assign pos k1 k2

      | _, None ->
          assign pos k2 k1

      | Some (App (t1, t2)), Some (App (t1', t2')) ->
          unify pos t1 t1';
          unify pos t2 t2')

let rec infer env t =
  match t.type_expr with
    | TE_tvar id ->
        lookup (TName (Location.value id)) (Location.loc id) env

    | TE_tapp (tc, ts) ->
        let k = variable () in
        let kd = List.fold_right (fun t acu ->
                     mkarrow (infer env t) acu
                   ) ts k in
        unify t.type_expr_loc (infer env tc) kd;
        k

and check env t k =
  unify t.type_expr_loc (infer env t) k

let rec intern_kind env = function
  | KStar -> star
  | KArrow (k1, k2) -> mkarrow (intern_kind env k1) (intern_kind env k2)
