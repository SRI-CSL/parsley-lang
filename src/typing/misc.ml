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

(** This module contains miscellaneous utilities. *)

(** [iter] is similar to [List.iter], but does not require [f] to
    return a result of type [unit]. Use with caution. *)
let rec iter f = function
  | []     -> ()
  | a :: l -> let _ = f a in
              iter f l

(** If [l] is a list of pairs of a key and a datum, and if [p] is a
    predicate on keys, then [assocp p l] returns the datum associated
    with the first key that satisfies [p] in [l]. It raises
    [Not_found] if no such key exists. *)
let rec assocp p = function
  | [] ->
      raise Not_found
  | (key, data) :: l ->
      if p key then data else assocp p l

(** Maps over strings. *)
module StringMap = struct
  include Map.Make(String)

  exception Strict of string

  let strict_add key data m =
    match find_opt key m with
      | Some _ -> raise (Strict key)
      | None   -> add key data m

  let strict_union m1 m2 =
    fold strict_add m1 m2
end

(** Prints a list of elements, with one occurrence of the separator
    between every two consecutive elements. *)
let print_separated_list separator print_elem xs =
  let rec loop x = function
    | []      -> print_elem x
    | y :: xs -> print_elem x ^ separator ^ loop y xs in
  match xs with
  | []      -> ""
  | x :: xs -> loop x xs

let rec last = function
  | []     -> raise Not_found
  | [ a ]  -> a
  | _ :: q -> last q

let twice f x y = (f x, f y)

let default d = function
  | Some x -> x
  | None   -> d

exception InvalidOptionUse

let unSome = function
  | None   -> raise InvalidOptionUse
  | Some x -> x

let array_associ_opt x a =
  let len = Array.length a in
  let rec chop i =
    if   i < len
    then if   fst a.(i) = x
         then Some i
         else chop (i + 1)
    else None in
  chop 0

let proj1_3 (x,_,_) = x
let proj2_3 (_,y,_) = y
let proj3_3 (_,_,z) = z
