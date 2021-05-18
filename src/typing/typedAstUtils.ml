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

let lookup_bitfield_length tenv t =
  let tn = Location.value t in
  let l  = Location.loc t in
  let tt = TName tn in
  let adt = match TEnv.lookup_adt tenv tt with
      | None ->
          let err = TExc.UnboundRecord (l, tt) in
          raise (TExc.Error err)
      | Some adt ->
          adt in
  match adt with
    | {adt = Variant _; _} ->
        let err = TExc.NotRecordType t in
        raise (TExc.Error err)
    | {adt = Record {bitfield_length = None; _}; _} ->
        let err = TExc.NotBitfieldType t in
        raise (TExc.Error err)
    | {adt = Record {bitfield_length = Some len; _}; _} ->
        len

(* A helper to check if a bound for the repeat combinator is
 * non-zero. It uses a primitive constant-folder that does not access
 * the environment; a better approach would be to have an actual
 * const-folding pass before this analysis.
 *
 * NOTE: The below const-folder strips type annotations for
 * simplicity, and so the result cannot be used to replace the source
 * argument. *)

let rec const_fold: 't 'v. ('t, 'v) expr -> ('t, 'v) expr =
  fun e ->
  match e.expr with
    | E_var _ | E_literal _ | E_mod_member _ | E_apply _ | E_constr _ ->
        e
    | E_match _ | E_record _ | E_field _ | E_let _ | E_case _ ->
        (* although these could be reduced in theory, it is unlikely
         * to be useful in this context *)
        e
    | E_cast (e, _) ->
        (* this loses information, but that's ok as long as we don't
         * replace the source with the result *)
        const_fold e
    | E_unop (op, e') ->
        let e' = const_fold e' in
        (match op, e'.expr with
          | Uminus, E_literal (PL_int i) ->
              {e with expr = E_literal (PL_int (~- i))}
          | Not, E_literal (PL_bool b) ->
              {e with expr = E_literal (PL_bool (not b))}
          | _ ->
              {e with expr = E_unop (op, e')})
    | E_binop (op, l, r) ->
        let l', r' = const_fold l, const_fold r in
        (match op, l'.expr, r'.expr with
           | Lt,   E_literal (PL_int l), E_literal (PL_int r) ->
               {e with expr = E_literal (PL_bool (l < r))}
           | Gt,   E_literal (PL_int l), E_literal (PL_int r) ->
               {e with expr = E_literal (PL_bool (l > r))}
           | Lteq, E_literal (PL_int l), E_literal (PL_int r) ->
               {e with expr = E_literal (PL_bool (l <= r))}
           | Gteq, E_literal (PL_int l), E_literal (PL_int r) ->
               {e with expr = E_literal (PL_bool (l >= r))}
           | Plus, E_literal (PL_int l), E_literal (PL_int r) ->
               {e with expr = E_literal (PL_int (l + r))}
           | Minus, E_literal (PL_int l), E_literal (PL_int r) ->
               {e with expr = E_literal (PL_int (l - r))}
           | Mult, E_literal (PL_int l), E_literal (PL_int r) ->
               {e with expr = E_literal (PL_int (l * r))}
           | Div,  E_literal (PL_int _), E_literal (PL_int r)
                when r = 0 ->
               raise (TExc.Error (TExc.Possible_division_by_zero e.expr_loc))
           | Div,  E_literal (PL_int l), E_literal (PL_int r) ->
               {e with expr = E_literal (PL_int (l / r))}
           | Land, E_literal (PL_bool l), E_literal (PL_bool r) ->
               {e with expr = E_literal (PL_bool (l && r))}
           | Lor,  E_literal (PL_bool l), E_literal (PL_bool r) ->
               {e with expr = E_literal (PL_bool (l || r))}
           (* Eq and Neq are polymorphic *)
           | Eq,   E_literal (PL_int l), E_literal (PL_int r) ->
               {e with expr = E_literal (PL_bool (l = r))}
           | Eq,   E_literal (PL_string l), E_literal (PL_string r) ->
               {e with expr = E_literal (PL_bool (l = r))}
           | Eq,   E_literal PL_unit, E_literal PL_unit ->
               {e with expr = E_literal (PL_bool true)}
           | Eq,   E_literal (PL_bool l), E_literal (PL_bool r) ->
               {e with expr = E_literal (PL_bool (l = r))}
           | Neq,  E_literal (PL_int l), E_literal (PL_int r) ->
               {e with expr = E_literal (PL_bool (not (l = r)))}
           | Neq,  E_literal (PL_string l), E_literal (PL_string r) ->
               {e with expr = E_literal (PL_bool (not (l = r)))}
           | Neq,  E_literal PL_unit, E_literal PL_unit ->
               {e with expr = E_literal (PL_bool false)}
           | Neq,  E_literal (PL_bool l), E_literal (PL_bool r) ->
               {e with expr = E_literal (PL_bool (not (l = r)))}
           | _ ->
               {e with expr = E_binop (op, l', r')})
    | E_recop (t, rop, e') ->
        {e with expr = E_recop (t, rop, const_fold e')}
    | E_bitrange (e', n, m) ->
        {e with expr = E_bitrange (const_fold e', n, m)}

let is_non_zero: 't 'v. ('t, 'v) expr -> bool =
  fun e ->
  match (const_fold e).expr with
    | E_literal (PL_int i) -> i != 0
    | _                    -> true
