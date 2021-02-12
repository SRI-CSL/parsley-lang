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

open Parsing
open Ast

module ME = MultiEquation
module TEnv = TypingEnvironment
module TExc = TypingExceptions

(* expanding type abbreviations in a type expression *)
let expand_type_abbrevs env te =
  let rec expand te =
    let loc = te.type_expr_loc in
    match te.type_expr with
      | TE_tvar t ->
          let tc = TName (Location.value t) in
          (match TEnv.lookup_type_abbrev env tc with
             | None -> te
             | Some abb ->
                 let n = List.length abb.TEnv.type_abbrev_tvars in
                 if n = 0
                 then abb.TEnv.type_abbrev_type
                 else let err =
                        TExc.PartialTypeConstructorApplication (loc, tc, n, 0)
                      in raise (TExc.Error err))
      | TE_tapp ({type_expr = TE_tvar t; _} as c, args) ->
          let tc = TName (Location.value t) in
          (match TEnv.lookup_type_abbrev env tc with
             | None ->
                 let args' = List.map expand args in
                 {te with type_expr = TE_tapp (c, args')}
             | Some abb ->
                 let n = List.length abb.TEnv.type_abbrev_tvars in
                 if n != List.length args
                 then
                   let err =
                     TExc.PartialTypeConstructorApplication
                       (loc, tc, n, List.length args)
                   in raise (TExc.Error err)
                 else
                   let args' = List.map expand args in
                   let map = List.combine abb.TEnv.type_abbrev_tvars args' in
                   subst map abb.TEnv.type_abbrev_type
          )

      | TE_tapp (c, args) ->
          let c' = expand c in
          let args' = List.map expand args in
          {te with type_expr = TE_tapp (c', args')}

  and subst map te =
    match te.type_expr with
      | TE_tvar t ->
          let s = Location.value t in
          (match List.assoc_opt (TName s) map with
             | None -> te
             | Some te -> te)
      | TE_tapp (c, args) ->
          let c' = subst map c in
          let args' = List.map (subst map) args in
          {te with type_expr = TE_tapp (c', args')}

  in expand te
