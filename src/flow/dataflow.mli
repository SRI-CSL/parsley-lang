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

open Block
open Graph

(* Dataflow lattices *)

type change_flag =
  | NoChange
  | SomeChange

module type LATTICE =
  sig
    type t
    val bottom: t
    val join: t -> t -> change_flag * t
  end

module type FACTBASE =
  sig
    (* Lattice structure *)
    type f
    val bottom: f
    val join: f -> f -> change_flag * f

    (* A factbase maps a label to a fact.  In the analysis engine,
     * the fact is the one at the entry of the block with that
     * label. *)
    type factbase = f Label.LabelMap.t

    val mk_factbase: (Label.label * f) list -> factbase

    (* [lookup fb l] requires that label [l] is present in [fb] *)
    val lookup:   factbase -> Label.label -> f option

    (* [get_fact fb l] returns the fact for [l] if [l] is present in
     * [fb], or L.bottom otherwise *)
    val get_fact: factbase -> Label.label -> f

    (* [add fb l f] adds fact [f] for [l] to [fb].  Note: the caller
     * is expected to do the join with any existing fact for [l] in
     * [fb]. *)
    val add: factbase -> Label.label -> f -> factbase
  end

module MkFactBase (L: LATTICE) : FACTBASE
     with type f = L.t

module type ANALYSIS =
  sig
    module G     : GRAPH
    module FB    : FACTBASE

    type direction =
      | Forward
      | Backward

    (* A graph open at the starting point has a single entry point,
     * and a single fact at that point.  A closed graph could have
     * multiple starting points with a fact at each.  The same applies
     * to the result of the pass at the ending point.  The starting
     * and ending points depend on the direction of the analysis.
     *)
    type 'd facts =
      | Facts_open:   FB.f        -> o facts
      | Facts_closed: FB.factbase -> c facts

    (* The forward node transfer function by node shape *)
    type ('v) fwd_transfer =
      ( ((c, o, 'v) G.Block.node -> c facts -> o facts)
      * ((o, o, 'v) G.Block.node -> o facts -> o facts)
      * ((o, c, 'v) G.Block.node -> o facts -> c facts)
      )

    (* The backward node transfer function by node shape. Note that
     * the backward transfer for a [(c, o) block] ends with a single
     * fact (i.e. an [o facts]) at the head node.  So the result fact
     * is always an [o facts]. *)
    type ('v) bwd_transfer =
      ( ((c, o, 'v) G.Block.node -> o facts -> o facts)
      * ((o, o, 'v) G.Block.node -> o facts -> o facts)
      * ((o, c, 'v) G.Block.node -> c facts -> o facts)
      )

    (* Forward dataflow analysis that takes a list of entry points
     * for graphs that are closed at entry, and returns the facts at
     * the graph exit(s), along with any facts for the body *)
    val fwd_analysis: 'e facts
                      -> ('e, Label.label list) maybeC
                      -> ('e, 'x, 'v) G.graph
                      -> 'v fwd_transfer
                      -> 'x facts * FB.factbase option
  end

module MkAnalysis (Graph: GRAPH) (Factbase: FACTBASE) : ANALYSIS
       with type FB.f                       = Factbase.f
        and type FB.factbase                = Factbase.factbase
        and type ('e, 'x, 'v) G.Block.node  = ('e, 'x, 'v) Graph.Block.node
        and type ('e, 'x, 'v) G.Block.block = ('e, 'x, 'v) Graph.Block.block
        and type ('e, 'x, 'v) G.graph       = ('e, 'x, 'v) Graph.graph
