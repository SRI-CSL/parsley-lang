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
open Label

type error =
  | Label_collision of label
exception GraphError of error

module type BODY =
  sig
    module Block : BLOCK

    type ('v) body = (c, c, 'v) Block.block Label.LabelMap.t

    val empty: 't Label.LabelMap.t
    val union: 'v body -> 'v body -> 'v body
    val to_list: 'v body -> (Label.label * (c, c, 'v) Block.block) list
    val add_block: 'v body -> (c, c, 'v) Block.block -> 'v body
  end

module type GRAPH =
  sig
    module Block : BLOCK
    module Body  : BODY
           with type ('e, 'x, 'v) Block.node = ('e, 'x, 'v) Block.node
            and type ('e, 'x, 'v) Block.block = ('e, 'x, 'v) Block.block

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

    (* traversal *)

    type error =
      | Unbound_label of Label.label (* label does not map to a block *)
    exception GraphError of error

    val rev_postorder: 'v Body.body -> Label.label -> (c, c, 'v) Block.block list

  end

module MkBody =
  functor (N: NODE) ->
  struct
    module Block = MkBlock (N)

    (* A body is a collection of closed/closed blocks indexed by their
     * entry labels.
     *)
    type ('v) body = (c, c, 'v) Block.block LabelMap.t

    let empty = LabelMap.empty

    let union (type v) (l: v body) (r: v body) : v body =
      let combine k _ _ =
        let err = Label_collision k in
        raise (GraphError err) in
      LabelMap.union combine l r

    let to_list (type v) (b: v body)
        : (Label.label * (c, c, v) Block.block) list =
      LabelMap.bindings b

    let add_block (type v) body (b: (c, c, v) Block.block) =
      let l = Block.entry_label b in
      if LabelMap.mem l body
      then let err = Label_collision l in
           raise (GraphError err)
      else LabelMap.add l b body
  end

module MkGraph =
  functor (N: NODE) ->
  struct
    module Block = MkBlock (N)
    module Body  = MkBody (N)

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
    let from_body (type v) b : (c, c, v) graph =
      GMany (NothingO, b, NothingO)

    (* from a block *)
    let unitOO (type v) (b: (o, o, v) Block.block)
        : (o, o, v) graph =
      GUnit b
    let unitOC (type v) (b: (o, c, v) Block.block)
        : (o, c, v) graph =
      GMany (JustO b, Body.empty, NothingO)
    let unitCO (type v) (b: (c, o, v) Block.block)
        : (c, o, v) graph =
      GMany (NothingO, Body.empty, JustO b)
    let unitCC (type v) (b: (c, c, v) Block.block)
        : (c, c, v) graph =
      GMany (NothingO, Body.add_block Body.empty b, NothingO)
    let of_block (type e x v) (b: (e, x, v) Block.block)
        : (e, x, v) graph =
      match b with
        | Block.BlockCO _ -> unitCO b
        | Block.BlockCC _ -> unitCC b
        | Block.BlockOC _ -> unitOC b
        | Block.BNil      -> GNil
        | Block.BMiddle _ -> unitOO b
        | Block.BCat _    -> unitOO b
        | Block.BSnoc _   -> unitOO b
        | Block.BCons _   -> unitOO b

    (* mapping *)

    let map_blocks: type e x v v'.
                         ( ((c, c, v) Block.block -> (c, c, v') Block.block)
                         * ((c, o, v) Block.block -> (c, o, v') Block.block)
                         * ((o, c, v) Block.block -> (o, c, v') Block.block)
                         * ((o, o, v) Block.block -> (o, o, v') Block.block) )
                         -> (e, x, v) graph
                         -> (e, x, v') graph =
      fun (mcc, mco, moc, moo) g ->
      let map_body = LabelMap.map mcc in
      match g with
        | GNil ->
            GNil
        | GUnit b ->
            GUnit (moo b)
        | GMany (NothingO, bd, NothingO) ->
            GMany (NothingO, map_body bd, NothingO)
        | GMany (NothingO, bd, JustO t) ->
            GMany (NothingO, map_body bd, JustO (mco t))
        | GMany (JustO h, bd, NothingO) ->
            GMany (JustO (moc h), map_body bd, NothingO)
        | GMany (JustO h, bd, JustO t) ->
            GMany (JustO (moc h), map_body bd, JustO (mco t))

    let map_nodes: type e x v v'.
                        ( ((c, o, v) Block.node -> (c, o, v') Block.node)
                        * ((o, o, v) Block.node -> (o, o, v') Block.node)
                        * ((o, c, v) Block.node -> (o, c, v') Block.node) )
                        -> (e, x, v) graph
                        -> (e, x, v') graph =
      fun maps g ->
      let map_body = LabelMap.map (Block.map maps) in
      match g with
        | GNil ->
            GNil
        | GUnit b ->
            GUnit (Block.map maps b)
        | GMany (NothingO, bd, NothingO) ->
            GMany (NothingO,
                   map_body bd,
                   NothingO)
        | GMany (NothingO, bd, JustO t) ->
            GMany (NothingO,
                   map_body bd,
                   JustO (Block.map maps t))
        | GMany (JustO h, bd, NothingO) ->
            GMany (JustO (Block.map maps h),
                   map_body bd,
                   NothingO)
        | GMany (JustO h, bd, JustO t) ->
            GMany (JustO (Block.map maps h),
                   map_body bd,
                   JustO (Block.map maps t))

    (* traversal *)

    (* An ordering of blocks in graph for traversals through the graph,
     * computed by a depth-first search from a given entry point.
     *
     * The function below returns the reverse postorder of the DFS
     * traversal, which is typically useful for forward analysis.  For
     * backward analysis, the returned order can be simply reversed.
     *
     * The algorithm below is taken from the implementation in GHC.
     *)

    (* entries in the working stack for DFS *)
    type 'n dfs_stack =
      | Nil
      | ConsTodo of 'n * 'n dfs_stack (* process if not visited already *)
      | ConsMark of 'n * 'n dfs_stack (* successors are done, ready for result *)

    type error =
      | Unbound_label of Label.label (* label does not map to a block *)
    exception GraphError of error

    let rev_postorder (type v) (graph: v Body.body) (entry: Label.label)
        : (c, c, v) Block.block list =
      let lookup_for_work work l =
        match LabelMap.find_opt l graph with
          | None   -> let err = Unbound_label l in
                      raise (GraphError err)
          | Some b -> ConsTodo (b, work) in
      let rec collect work in_progress accum =
        match work with
          | Nil ->
              accum
          | ConsMark (b, work) ->
              collect work in_progress (b :: accum)
          | ConsTodo (b, work) ->
              let l = Block.entry_label b in
              if LabelSet.mem l in_progress
              then collect work in_progress accum
              else
                let in_progress = LabelSet.add l in_progress in
                let work =
                  List.fold_left lookup_for_work
                    (ConsMark (b, work)) (Block.successors b) in
                collect work in_progress accum in
      let start = lookup_for_work Nil entry in
      collect start LabelSet.empty []

  end
