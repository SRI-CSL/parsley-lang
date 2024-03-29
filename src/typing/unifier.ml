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

(** This module implements unification of (ranked) multi-equations
    over a free algebra.

    For the purposes of this module, a rank is an element of an
    arbitrary total order. A rank is associated with every
    multi-equation. When two multi-equations are merged, the smaller
    rank is kept.

    It is understood that finite and infinite terms are legal -- no
    occur check is performed here. *)

open CoreAlgebra
open MultiEquation

type unify_error =
  CannotUnify of crterm * crterm

exception Error of Parsing.Location.t * unify_error

(* [unify register v1 v2] equates the variables [v1] and [v2]. That
   is, it adds the equation [v1 = v2] to the constraint which it
   maintains, then rewrites it in a number of ways until an
   inconsistency is found or a solved form is reached. If the
   former, then [CannotUnify] is raised.

   Any variables which are freshly created during the process are
   passed to [register], so as to make the caller aware of their
   existence. *)

let unify ?tracer pos register =
  let tracer = Misc.default (fun _ -> ignore) tracer in

  (* Define an auxiliary function which creates a fresh variable,
     found within a multi-equation of its own, with specified
     rank and structure. *)
  let fresh ?name kind rank structure =
    let v = UnionFind.fresh
              {structure = structure;
               rank = rank;
               mark = Mark.none;
               kind = kind;
               name = name;
               pos  = None;
               var  = None}   in
    register v;
    v in

  (* The main function only has two parameters; [register] remains
     unchanged through recursive calls. *)
  let rec unify pos (v1: variable) (v2: variable) =
    tracer v1 v2;

    (* If the two variables already belong to the same multi-equation,
       there is nothing to do. This check is not just an optimization;
       it is essential in guaranteeing termination, since we are
       dealing with potentially cyclic structures. *)
    if not (UnionFind.equivalent v1 v2) then

      (* Before performing a recursive call, we will merge the
         multi-equations associated with [v1] and [v2]. We can't
         do this right here and now, however, because we need to
         look at their structure to determine which descriptor it
         is best (more economical) to keep. *)
      let desc1 = UnionFind.find v1
      and desc2 = UnionFind.find v2 in

      (* Our first step is to compare the ranks of the two multi-equations,
         so as to compute the minimum rank.

         This enables us to give correct and efficient versions of a number
         of auxiliary functions:

         [fresh]  specializes [fresh] (defined above) with the minimum rank.
         [merge]  merges the multi-equations, keeping an arbitrary structure.
         [merge1] merges the multi-equations, keeping the former's structure.
         [merge2] merges the multi-equations, keeping the latter's structure.
      *)
      let _fresh, merge, merge1, merge2 =
        let kind =
          match desc1.kind, desc2.kind with
            | k1, _k2 when is_rigid v1 -> k1
            | _k1, k2 when is_rigid v2 -> k2
            | _                        -> Flexible in
        let name =
          match desc1.name, desc2.name with
            | Some name1, Some name2 ->
                if   name1 <> name2
                then if      is_rigid v1
                     then    Some name1
                     else if is_rigid v2
                     then    Some name2
                     else    None
                else Some name1
            | Some name, _
            | _, Some name -> Some name
            | _            -> None in
        let rank1 = desc1.rank
        and rank2 = desc2.rank in
        if   IntRank.compare rank1 rank2 < 0
        then let merge1 () =
               UnionFind.union v2 v1;
               desc1.kind <- kind;
               desc1.name <- name
             and merge2 () =
               UnionFind.union v2 v1;
               desc1.kind <- kind;
               desc1.name <- name;
               desc1.structure <- desc2.structure in
             fresh ?name:name kind rank1, merge1, merge1, merge2
        else let merge1 () =
               UnionFind.union v1 v2;
               desc2.structure <- desc1.structure;
               desc2.kind <- kind;
               desc2.name <- name
             and merge2 () =
               UnionFind.union v1 v2;
               desc2.kind <- kind;
               desc2.name <- name in
             fresh ?name:name kind rank2, merge2, merge1, merge2 in

      (* Now, let us look at the structure of the two multi-equations. *)
      match desc1.structure, desc2.structure, merge1, merge2 with
        (* Neither multi-equation contains a term.
           Merge them; we're done. *)
        | None, None, _, _ when is_flexible v1 && is_flexible v2 ->
            merge ()
        | None, _, _, _ when is_flexible v1 ->
            merge2 ();
        | _, None, _, _ when is_flexible v2 ->
            merge1 ();

        (* Exactly one multi-equation contains a term; keep it. *)
        | Some (Var v), _, _, _ ->
            unify pos v v2
        | _, Some (Var v), _, _ ->
            unify pos v v1

        (* It is forbidden to unify rigid type variables with
           a structure. *)
        | None, _, _, _ (* v1 is rigid. *) ->
            raise (Error (pos, CannotUnify (TVariable v1, TVariable v2)))
        | _, None, _, _ (* v2 is rigid. *) ->
            raise (Error (pos, CannotUnify (TVariable v2, TVariable v1)))

        (* Both multi-equations contain terms whose head symbol belong
           to the free algebra [A]. Merge the multi-equations
           (dropping one of the terms), then decompose the equation
           that arises between the two terms. Signal an error if the
           terms are incompatible, i.e. do not have the same head
           symbol. *)
        | Some (App (term1, term2)), Some (App (term1', term2')), _, _ ->
            begin
              merge();
              unify pos term1 term1';
              unify pos term2 term2'
            end in

  unify pos

open TypeConstraintPrinter
let error_msg = function
  | CannotUnify (r, t) ->
      Printf.sprintf "%s and %s are not compatible."
        (print_crterm t) (print_crterm r)
