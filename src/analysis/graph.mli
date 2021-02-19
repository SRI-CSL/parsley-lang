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

type error =
  | Label_collision of Label.label
exception GraphError of error

module type BODY =
  sig
    module Block : BLOCK

    (* A body is a collection of closed/closed blocks indexed by their
     * entry labels.
     *)
    type ('v) body = (c, c, 'v) Block.block Label.LabelMap.t

    val empty: 't Label.LabelMap.t

    val union: 'v body -> 'v body -> 'v body

    val to_list: 'v body -> (Label.label * (c, c, 'v) Block.block) list

    val add_block: 'v body -> (c, c, 'v) Block.block -> 'v body

  end

module MkBody (N: NODE) : BODY
       with type ('e, 'x, 'v) Block.node = ('e, 'x, 'v) N.node

module type GRAPH =
  sig
    module Block : BLOCK
    module Body  : BODY
           with type ('e, 'x, 'v) Block.node  = ('e, 'x, 'v) Block.node
            and type ('e, 'x, 'v) Block.block = ('e, 'x, 'v) Block.block

    (* A control flow graph.  It can have four shapes: O/O, O/C, C/O,
     * C/C.  A graph open at the entry has a single, distinguished,
     * anonymous entry point.  If a graph is closed at the entry,
     * its entry point(s) are supplied by an external context.
     *)
    type ('e, 'x, 'v) graph =
      | GNil:                            (o, o, 'v) graph
      | GUnit: (o, o, 'v) Block.block -> (o, o, 'v) graph
      | GMany:
            ('e, (o, c, 'v) Block.block) maybeO
          * 'v Body.body
          * ('x, (c, o, 'v) Block.block) maybeO
            -> ('e, 'x, 'v) graph

    (* constructing graphs *)

    (* from a body *)
    val from_body: 'v Body.body -> (c, c, 'v) graph

    (* from a block *)
    val unitOO: (o, o, 'v) Block.block -> (o, o, 'v) graph
    val unitOC: (o, c, 'v) Block.block -> (o, c, 'v) graph
    val unitCO: (c, o, 'v) Block.block -> (c, o, 'v) graph
    val unitCC: (c, c, 'v) Block.block -> (c, c, 'v) graph

    val of_block: ('e, 'x, 'v) Block.block -> ('e, 'x, 'v) graph

    (* extending graphs with nodes *)

    val catGraphNodeOO: ('e, o, 'v) graph -> (o, o, 'v) Block.node -> ('e, o, 'v) graph
    val catGraphNodeOC: ('e, o, 'v) graph -> (o, c, 'v) Block.node -> ('e, c, 'v) graph

    val catNodeOOGraph: (o, o, 'v) Block.node -> (o, 'x, 'v) graph -> (o, 'x, 'v) graph
    val catNodeCOGraph: (c, o, 'v) Block.node -> (o, 'x, 'v) graph -> (c, 'x, 'v) graph

    (* splicing graphs *)

    val splice: ('e, 'a, 'v) graph -> ('a, 'x, 'v) graph -> ('e, 'x, 'v) graph

    (* mapping *)

    val map_blocks: ( ((c, c, 'v) Block.block -> (c, c, 'w) Block.block)
                    * ((c, o, 'v) Block.block -> (c, o, 'w) Block.block)
                    * ((o, c, 'v) Block.block -> (o, c, 'w) Block.block)
                    * ((o, o, 'v) Block.block -> (o, o, 'w) Block.block) )
                    -> ('e, 'x, 'v) graph
                    -> ('e, 'x, 'w) graph

    val map_nodes:  ( ((c, o, 'v) Block.node -> (c, o, 'w) Block.node)
                    * ((o, o, 'v) Block.node -> (o, o, 'w) Block.node)
                    * ((o, c, 'v) Block.node -> (o, c, 'w) Block.node) )
                    -> ('e, 'x, 'v) graph
                    -> ('e, 'x, 'w) graph

    (* folding *)

    (* forward folding is used for blocks *)
    val fold_nodes: ( ((c, o, 'v) Block.node -> 'a -> 'a)
                    * ((o, o, 'v) Block.node -> 'a -> 'a)
                    * ((o, c, 'v) Block.node -> 'a -> 'a) )
                    -> ('e, 'x, 'v) graph -> 'a -> 'a

    (* traversal *)

    (* An ordering of blocks in graph for traversals through the graph,
     * computed by a depth-first search from a given entry point.
     *)

    type error =
      | Unbound_label of Label.label (* label does not map to a block *)
    exception GraphError of error

    val rev_postorder: 'v Body.body -> Label.label -> (c, c, 'v) Block.block list

  end

module MkGraph (N: NODE) : GRAPH
       with type ('e, 'x, 'v) Block.node = ('e, 'x, 'v) N.node
        and type ('e, 'x, 'v) Body.Block.node = ('e, 'x, 'v) N.node
