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

(** This module implements an environment. *)

type ('a, 'b) t = ('a * 'b) list

let lookup env x =
  List.assoc x env

let lookup_opt env x =
  List.assoc_opt x env

let filter env f =
  List.fold_left (fun acu (_, x) -> if f x then x :: acu else acu) [] env

let add env x t =
  (x, t) :: env

let empty  = []
let concat = ( @ )

let iter      = List.iter
let fold_left = List.fold_left
let map       = List.map
