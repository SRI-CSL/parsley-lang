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
val iter: ('a -> 'b) -> 'a list -> unit

(** If [l] is a list of pairs of a key and a datum, and if [p] is a
    predicate on keys, then [assocp p l] returns the datum associated
    with the first key that satisfies [p] in [l]. It raises
    [Not_found] if no such key exists. *)
val assocp: ('a -> bool) -> ('a * 'b) list -> 'b

(** Maps over strings. *)
module StringMap : sig

  include Map.S with type key = string

  exception Strict of string

  (** raises `Strict` if there are keys in common *)
  val strict_union: 'a t -> 'a t -> 'a t

end with type key = string

(** Prints a list of elements, with one occurrence of the separator
    between every two consecutive elements. *)
val print_separated_list: string -> ('a -> string) -> 'a list -> string

(** Returns the last element of a list. Linear complexity. *)
val last : 'a list -> 'a

val twice : ('a -> 'b) -> 'a -> 'a -> ('b * 'b)

exception InvalidOptionUse

val default : 'a -> 'a option -> 'a

val unSome : 'a option -> 'a

val array_associ_opt : 'a -> ('a * 'b) array -> int option

val proj1_3 : ('a * 'b * 'c) -> 'a
val proj2_3 : ('a * 'b * 'c) -> 'b
val proj3_3 : ('a * 'b * 'c) -> 'c
