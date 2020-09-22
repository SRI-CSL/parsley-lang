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

(** This module implements a core algebra of first order terms.

    The type core algebra contains all the first order terms built using
    the following four symbols:

    [RowCons] is the row constructor which appends a label to a row.
    [RowUniform] denotes the row which maps every label to a particular term.
    [App] is the application of a type to another type.
    [Var] is a type variable.

    This definition is later augmented in {!TypeAlgebra}. *)

(** [lname] is the type of label. *)
type lname = LName of string

(** {3 Type as tree} *)

(** Terms whose parameters are of type ['a]. This data structure
    represents a tree whose depth is exactly equal to 1. *)
type 'a term =
  | App of 'a * 'a
  | Var of 'a

(** Terms whose parameters are either leaves of type ['a], or terms.
    [arterm] stands for ``abstract recursive term''. *)
type 'a arterm =
  | TVariable of 'a
  | TTerm of ('a arterm) term

(** {3 Usual higher order functions} *)

(** [iter f term] applies [f] successively to every parameter of
    the term [term]. *)
val iter: ('a -> unit) -> 'a term -> unit

(** [map f term] returns a term whose head symbol is that of [term]
    and whose parameters are the images of [term]'s parameters
    through [f]. *)
val map: ('a -> 'b) -> 'a term -> 'b term

(** [fold f term accu] folds [f] over [term]'s parameters, using
    [accu] as initial value. *)
val fold: ('a -> 'b -> 'b) -> 'a term -> 'b -> 'b

(** [fold2 f term term' accu] folds [f] over [term]'s parameters, using
    [accu] as initial value. *)
val fold2: ('a -> 'b -> 'c -> 'c) -> 'a term -> 'b term -> 'c -> 'c

(** {3 Type manipulation} *)

val change_arterm_vars : ('a * 'a) list -> 'a arterm -> 'a arterm

(** [app t ts] built the term corresponding to the [(...((t t0) t1)... tn)]. *)
val app : 'a arterm -> 'a arterm list -> 'a arterm
