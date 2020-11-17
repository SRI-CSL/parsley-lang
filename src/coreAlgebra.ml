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

(** [lname] is the type of label. *)
type lname = LName of string

(** This module implements the internal representation of terms. *)

(** The terms of the underlying free algebra. *)
type 'a term =
  | App of 'a * 'a
  | Var of 'a

(** Terms whose parameters are either leaves of type ['a], or terms.
    [arterm] stands for ``abstract recursive term''. *)
type 'a arterm =
  | TVariable of 'a
  | TTerm of ('a arterm) term

let iter f = function
  | App (l, r) ->
      f l; f r
  | Var v ->
      f v

let map f = function
  | App (l, r) ->
      App (f l, f r)
  | Var v ->
      Var (f v)

let fold f term accu =
  match term with
    | App (l, r) ->
        f r (f l accu)
    | Var v ->
        f v accu

let fold2 f term term' accu =
  match term, term' with
    | App (l, r), App (l', r') ->
        f r r' (f l l' accu)
    | Var v, Var v' ->
        f v v' accu
    | _ -> failwith "fold2"

let app t args =
  List.fold_left (fun acu x -> TTerm (App (acu, x))) t args

let rec change_term_vars c =
  map (change_arterm_vars c)

and change_arterm_vars c =
  function
    | TTerm term -> TTerm (change_term_vars c term)
    | TVariable x -> TVariable (
        match List.assq_opt x c with
          | Some y -> y
          | None -> x)
