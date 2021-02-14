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

module MkBody =
  functor (N: NODE) ->
  struct
    module Block = MkBlock(N)

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
    module Block = MkBlock(N)
    module Body  = MkBody(N)

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

    (* extending graphs with nodes *)

    let catGraphNodeOO (type e v)
          (g: (e, o, v) graph)
          (n: (o, o, v) N.node)
        : (e, o, v) graph =
      match g with
        | GNil ->
            unitOO (Block.BMiddle n)
        | GUnit b ->
            unitOO (Block.BSnoc (b, n))
        | GMany (e, b, JustO (Block.BlockCO (h, b'))) ->
            GMany (e, b, JustO (Block.BlockCO (h, Block.BSnoc (b', n))))
        (* not sure why the below branch is needed; it seems wrong *)
        | GMany (_, _, _) ->
            assert false

    let catGraphNodeOC (type e v)
          (g: (e, o, v) graph)
          (n: (o, c, v) N.node)
        : (e, c, v) graph =
      match g with
        | GNil ->
            unitOC (Block.BlockOC (Block.BNil, n))
        | GUnit b ->
            unitOC (Block.BlockOC (b, n))
        | GMany (e, bd, JustO (Block.BlockCO (h, b'))) ->
            let bl = Block.BlockCC (h, b', n) in
            GMany (e, Body.add_block bd bl, NothingO)
        (* not sure why the below branch is needed; it seems wrong *)
        | GMany (_, _, _) ->
            assert false

    let catNodeOOGraph (type x v)
          (n: (o, o, v) N.node)
          (g: (o, x, v) graph)
        : (o, x, v) graph =
      match g with
        | GNil ->
            unitOO (Block.BMiddle n)
        | GUnit b ->
            unitOO (Block.BCons (n, b))
        | GMany (JustO (Block.BlockOC (b', t)), b, x) ->
            let bl = Block.BCons (n, b') in
            GMany (JustO (Block.BlockOC (bl, t)), b, x)
        (* not sure why the below branch is needed; it seems wrong *)
        | GMany (_, _, _) ->
            assert false

    let catNodeCOGraph (type x v)
          (n: (c, o, v) N.node)
          (g: (o, x, v) graph)
        : (c, x, v) graph =
      match g with
        | GNil ->
            unitCO (Block.BlockCO (n, Block.BNil))
        | GUnit b ->
            unitCO (Block.BlockCO (n, b))
        | GMany (JustO (Block.BlockOC (b', t)), b, x) ->
            let bl = Block.BlockCC (n, b', t) in
            GMany (NothingO, Body.add_block b bl, x)
        (* not sure why the below branch is needed; it seems wrong *)
        | GMany (_, _, _) ->
            assert false


    (* splicing graphs *)

    let splice (type e a x v)
          (g1: (e, a, v) graph)
          (g2: (a, x, v) graph)
        : (e, x, v) graph =
      match g1, g2 with
        | GNil, _ ->
            g2
        | _, GNil ->
            g1
        | GUnit b1, GUnit b2 ->
            GUnit (Block.append b1 b2)
        | GUnit b1, GMany (JustO e, bd, x) ->
            GMany (JustO (Block.append b1 e), bd, x)
        | GMany (e, bd, JustO x), GUnit b2 ->
            GMany (e, bd, JustO (Block.append x b2))
        | GMany (e, bd1, JustO x1), GMany (JustO e2, bd2, x) ->
            let bd = Body.add_block bd1 (Block.append x1 e2) in
            let bd = Body.union bd bd2 in
            GMany (e, bd, x)
        | GMany (e, bd1, NothingO), GMany (NothingO, bd2, x) ->
            GMany (e, Body.union bd1 bd2, x)
        (* not sure why the below branches are needed; it seems wrong *)
        | GUnit _, GMany _
        | GMany _, GUnit _
        | GMany _, GMany _ ->
            assert false

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
                        ( ((c, o, v) N.node -> (c, o, v') N.node)
                        * ((o, o, v) N.node -> (o, o, v') N.node)
                        * ((o, c, v) N.node -> (o, c, v') N.node) )
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

    (* folding *)

    (* forward folding is used for blocks *)
    let fold_nodes: type a e x v.
                         ( ((c, o, v) N.node -> a -> a)
                         * ((o, o, v) N.node -> a -> a)
                         * ((o, c, v) N.node -> a -> a) )
                         -> (e, x, v) graph -> a -> a =
      fun maps g a ->
      let fold_body bd a =
        let foldr _ b a =
          Block.ffold maps b a in
        LabelMap.fold foldr bd a in
      match g with
        | GNil ->
            a
        | GUnit b ->
            a |> Block.ffold maps b
        | GMany (NothingO, bd, NothingO) ->
            a |> fold_body bd
        | GMany (NothingO, bd, JustO t) ->
            a |> fold_body bd |> Block.ffold maps t
        | GMany (JustO h, bd, NothingO) ->
            a |> Block.ffold maps h |> fold_body bd
        | GMany (JustO h, bd, JustO t) ->
            a |> Block.ffold maps h |> fold_body bd |> Block.ffold maps t

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
