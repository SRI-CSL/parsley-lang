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

(* basic graph module for dependency analysis *)

module type DepGraph = sig
  type node
  type t
  type cycle = node list

  val init: t
  val add_deps: t -> node -> node list -> (t, cycle) result
  val deps: t -> node -> node list option

  (* returns a topologically sorted node list if possible, returns a
     list of nodes in a cycle if not *)
  val topo_sort: t -> (node list, cycle) result
end

module Make (Ord: Set.OrderedType) : DepGraph
        with type node = Ord.t
