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
open Typing
open Anf

(* pattern action row, with integer labels for actions *)
type prow = pat list * int
(* pattern action matrix *)
type pmat = prow list

(* constructor of a type or wildcard *)
type con =
  | Con of (modul * string * string) * (* arity *) int
  | Lit of Ast.primitive_literal
  | Default

(* intermediate form for pattern match compilation *)
type decision_tree =
  (* The leaf indicates a successful match and provides the label for
     the action to execute for the match. *)
  | Leaf of int
  (* A switch indicates an incomplete match at an occurrence, and
     provides the decision tree to continue the match for each
     constructor at that occurrence. *)
  | Switch of occurrence * (con * typ * Location.t * decision_tree) list

(* compile pattern matching into a decision tree. *)
val to_decision_tree:
  TypingEnvironment.environment -> pmat -> Location.t -> decision_tree

(* computes the path occurrences for each pattern variable in a
   pattern *)
val pvar_paths: pat -> (TypeInfer.varid Ast.var * typ * occurrence) list

(* printers *)
val print_dectree: decision_tree -> unit
val print_pmat: pmat -> unit
