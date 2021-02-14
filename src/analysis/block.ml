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

type o  (* type indicator for Open   *)
type c  (* type indicator for Closed *)

type ('ex, 'a) maybeO =
  | JustO:    'a -> (o, 'a) maybeO
  | NothingO:       (c, 'a) maybeO

type ('ex, 'a) maybeC =
  | JustC:    'a -> (c, 'a) maybeC
  | NothingC:       (o, 'a) maybeC

type 'a shape =
  | Closed: c shape
  | Open:   o shape

module type NODE =
  sig
    (* Each node is indexed by entry ('e) and exit ('x) type
     * indicators that are instantiated by either o or c, and a
     * carrier indicator ('v) for nodes parameterized by
     * caller-specific information.
     *)
    type ('e, 'x, 'v) node

    val entry_label: (c, 'a, 'v) node -> Label.label
    val successors:  ('a, c, 'v) node -> Label.label list
  end

module MkBlock =
  functor (N: NODE) ->
  struct
    type ('e, 'x, 'v) node = ('e, 'x, 'v) N.node

    (* A block is a sequence of nodes.  Each end of the block could be
     * either open or closed, depending on the node at that end.
     * A block can hence be in one of four shapes: O/O, O/C, C/O, CC.
     * A block can be extended at any end that is open.  A C/C block
     * is a block that cannot be extended in any direction.
     *)
    type ('e, 'x, 'v) block =
      | BlockCO: (c, o, 'v) node  * (o, o, 'v) block                    -> (c, o, 'v) block
      | BlockCC: (c, o, 'v) node  * (o, o, 'v) block * (o, c, 'v) node  -> (c, c, 'v) block
      | BlockOC:                    (o, o, 'v) block * (o, c, 'v) node  -> (o, c, 'v) block

      | BNil:    (o, o, 'v) block
      | BMiddle: (o, o, 'v) node                     -> (o, o, 'v) block
      | BCat:    (o, o, 'v) block * (o, o, 'v) block -> (o, o, 'v) block
      | BSnoc:   (o, o, 'v) block * (o, o, 'v) node  -> (o, o, 'v) block
      | BCons:   (o, o, 'v) node  * (o, o, 'v) block -> (o, o, 'v) block

    let rec is_empty: type e x v . (e, x, v) block -> bool = function
      | BNil -> true
      | BCat (l, r) -> is_empty l && is_empty r
      | _ -> false

    (* labels *)

    let entry_label (type x v) (b: (c, x, v) block)
        : Label.label =
      match b with
        | BlockCO (h, _)
        | BlockCC (h, _, _) -> N.entry_label h

    let successors (type e v) (b: (e, c, v) block)
        : Label.label list =
      match b with
        | BlockCC (_, _, t)
        | BlockOC (_, t)    -> N.successors t

    (* construction *)

    let empty = BNil

    let rec cons: type x v.
                       (o, o, v) node
                       -> (o, x, v) block
                       -> (o, x, v) block =
      fun n b ->
      match b with
        | BlockOC (b, l) -> BlockOC ((cons n b), l)
        | BNil      -> BMiddle n
        | BMiddle _ -> BCons (n, b)
        | BCat _    -> BCons (n, b)
        | BSnoc _   -> BCons (n, b)
        | BCons _   -> BCons (n, b)

    let rec snoc: type e v.
                       (e, o, v) block
                       -> (o, o, v) node
                       -> (e, o, v) block =
      fun b n ->
      match b with
        | BlockCO (n', b) -> BlockCO (n', (snoc b n))
        | BNil      -> BMiddle n
        | BMiddle _ -> BSnoc (b, n)
        | BCat _    -> BSnoc (b, n)
        | BSnoc _   -> BSnoc (b, n)
        | BCons _   -> BSnoc (b, n)

    let join (type v)
          (h: (c, o, v) node)
          (b: (o, o, v) block)
          (t: (o, c, v) node)
        : (c, c, v) block =
      BlockCC (h, b, t)

    let join_head (type x v) (n: (c, o, v) node) (b: (o, x, v) block)
        : (c, x, v) block =
      match b with
        | BlockOC (b, n') -> BlockCC (n, b, n')
        | BNil            -> BlockCO (n, b)
        | BMiddle _       -> BlockCO (n, b)
        | BCat _          -> BlockCO (n, b)
        | BSnoc _         -> BlockCO (n, b)
        | BCons _         -> BlockCO (n, b)

    let join_tail (type e v) (b: (e, o, v) block) (n: (o, c, v) node)
        : (e, c, v) block =
      match b with
        | BlockCO (n', b) -> BlockCC (n', b, n)
        | BNil            -> BlockOC (b, n)
        | BMiddle _       -> BlockOC (b, n)
        | BCat _          -> BlockOC (b, n)
        | BSnoc _         -> BlockOC (b, n)
        | BCons _         -> BlockOC (b, n)

    let join_any (type e x v)
          (h: (e, (c, o, v) node) maybeC)
          (b: (o, o, v) block)
          (t: (x, (o, c, v) node) maybeC)
        : (e, x, v) block =
      match h, t with
        | JustC h, JustC t   -> BlockCC (h, b, t)
        | JustC h, NothingC  -> BlockCO (h, b)
        | NothingC, JustC t  -> BlockOC (b, t)
        | NothingC, NothingC -> b

    (* internal function *)
    let rec cat: type e x v.
                      (e, o, v) block
                      -> (o, x, v) block
                      -> (e, x, v) block =
      fun l r ->
      match l with
        | BlockCO (h, b) ->
            (match r with
               | BlockOC (b', t) -> BlockCC (h, cat b b', t)
               | BNil            -> l
               | BMiddle n       -> BlockCO (h, cat b (BMiddle n))
               | BCat (l', r')   -> BlockCO (h, cat b (BCat (l', r')))
               | BSnoc (b', n)   -> BlockCO (h, cat b (BSnoc (b', n)))
               | BCons (n, b')   -> BlockCO (h, cat b (BCons (n, b'))))
        | BNil ->
            r
        | BMiddle n ->
            (match r with
               | BlockOC (b, t) -> BlockOC (cat l b, t)
               | BNil           -> r
               | BMiddle _      -> BCons (n, r)
               | BCat _         -> BCons (n, r)
               | BSnoc _        -> BCons (n, r)
               | BCons _        -> BCons (n, r))
        | BCat _ ->
            (match r with
               | BlockOC (b, t) -> BlockOC (cat l b, t)
               | BNil      -> l
               | BMiddle n -> BSnoc (l, n)
               | BCat _    -> BCat (l, r)
               | BSnoc _   -> BCat (l, r)
               | BCons _   -> BCat (l, r))
        | BSnoc _ ->
            (match r with
               | BlockOC (b, t) -> BlockOC (cat l b, t)
               | BNil      -> l
               | BMiddle n -> BSnoc (l, n)
               | BCat _    -> BCat (l, r)
               | BSnoc _   -> BCat (l, r)
               | BCons _   -> BCat (l, r))
        | BCons _ ->
            (match r with
               | BlockOC (b, t) -> BlockOC (cat l b, t)
               | BNil      -> l
               | BMiddle n -> BSnoc (l, n)
               | BCat _    -> BCat (l, r)
               | BSnoc _   -> BCat (l, r)
               | BCons _   -> BCat (l, r))
    (* exposed name *)
    let append = cat

    (* deconstruction *)

    let first_node (type x v) (b: (c, x, v) block) : (c, o, v) node =
      match b with
        | BlockCO (n, _)    -> n
        | BlockCC (n, _, _) -> n

    let last_node (type e v) (b: (e, c, v) block) : (o, c, v) node =
      match b with
        | BlockCC (_, _, n) -> n
        | BlockOC (_, n)    -> n

    let end_nodes (type v) (b: (c, c, v) block)
        : (c, o, v) node * (o, c, v) node =
      match b with
        | BlockCC (e, _, x) -> e, x

    let split_head (type x v) (b: (c, x, v) block)
        : (c, o, v) node * (o, x, v) block =
      match b with
        | BlockCO (h, b)    -> h, b
        | BlockCC (h, b, t) -> h, BlockOC (b, t)

    let split_tail (type e v) (b: (e, c, v) block)
        : (e, o, v) block * (o, c, v) node =
      match b with
        | BlockOC (b, t)    -> b, t
        | BlockCC (e, b, t) -> BlockCO (e, b), t

    let split (type v) (b: (c, c, v) block)
        : (c, o, v) node * (o, o, v) block * (o, c, v) node =
      match b with
        | BlockCC (h, b, t) -> h, b, t

    let split_any (type e x v) (b: (e, x, v) block)
        : (e, (c, o, v) node) maybeC * (o, o, v) block * (x, (o, c, v) node) maybeC
      =
      match b with
        | BlockCO (h, b)    -> JustC h,  b, NothingC
        | BlockCC (h, b, t) -> JustC h,  b, JustC t
        | BlockOC (b, t)    -> NothingC, b, JustC t

        | BNil              -> NothingC, b, NothingC
        | BMiddle _         -> NothingC, b, NothingC
        | BCat _            -> NothingC, b, NothingC
        | BSnoc _           -> NothingC, b, NothingC
        | BCons _           -> NothingC, b, NothingC

    let to_list (type v) (b: (o, o, v) block) : (o, o, v) node list =
      let rec fold acc b =
        match b with
          | BNil         -> acc
          | BMiddle n    -> n :: acc
          | BCat (l, r)  -> fold (fold acc r) l
          | BSnoc (l, n) -> fold (n :: acc) l
          | BCons (n, l) -> n :: fold acc l in
      fold [] b

    let from_list (type v) (l: (o, o, v) node list) : (o, o, v) block =
      List.fold_right (fun n b -> BCons (n, b)) l BNil

    (* modification *)

    let replace_first_node (type x v)
          (b: (c, x, v) block)
          (n: (c, o, v) node)
        : (c, x, v) block =
      match b with
        | BlockCO (_, b)    -> BlockCO (n, b)
        | BlockCC (_, b, t) -> BlockCC (n, b, t)

    let replace_last_node (type e v)
          (b: (e, c, v) block)
          (n: (o, c, v) node)
        : (e, c, v) block =
      match b with
        | BlockCC (h, b, _) -> BlockCC (h, b, n)
        | BlockOC (b, _)    -> BlockOC (b, n)

    (* mapping *)

    let rec map: type e x v v'.
                      ( ((c, o, v) node -> (c, o, v') node)
                      * ((o, o, v) node -> (o, o, v') node)
                      * ((o, c, v) node -> (o, c, v') node) )
                      -> (e, x, v) block
                      -> (e, x, v') block =
      fun (mf, mm, ml) b ->
      let map' = map (mf, mm, ml) in
      match b with
        | BlockCO (h, b)    -> BlockCO (mf h, map' b)
        | BlockCC (h, b, t) -> BlockCC (mf h, map' b, ml t)
        | BlockOC (b, t)    -> BlockOC (map' b, ml t)
        | BNil              -> BNil
        | BMiddle n         -> BMiddle (mm n)
        | BCat (l, r)       -> BCat (map' l, map' r)
        | BSnoc (b, t)      -> BSnoc (map' b, mm t)
        | BCons (h, b)      -> BCons (mm h, map' b)

    (* folding forward and backward *)

    let ffold: type a e x v.
                    ( ((c, o, v) node -> a -> a)
                    * ((o, o, v) node -> a -> a)
                    * ((o, c, v) node -> a -> a) )
                    -> (e, x, v) block -> a -> a =
      fun (ff, fm, fl) b a ->
      let rec fold: type e x. (e, x, v) block -> a -> a =
        fun b a ->
        match b with
          | BlockCO (h, b)    -> a |> ff h |> fold b
          | BlockCC (h, b, t) -> a |> ff h |> fold b |> fl t
          | BlockOC (b, t)    -> a         |> fold b |> fl t
          | BNil              -> a
          | BMiddle n         -> a |> fm n
          | BCat (l, r)       -> a |> fold l |> fold r
          | BSnoc (b, n)      -> a |> fold b |> fm n
          | BCons (n, b)      -> a |> fm n   |> fold b in
      fold b a

    let bfold:
          type a e x v. ( ((c, o, v) node -> a -> a)
                        * ((o, o, v) node -> a -> a)
                        * ((o, c, v) node -> a -> a) )
               -> (e, x, v) block -> a -> a =
      fun (ff, fm, fl) b a ->
      let rec fold: type e x. (e, x, v) block -> a -> a =
        fun b a ->
        match b with
          | BlockCO (h, b)    -> a         |> fold b |> ff h
          | BlockCC (h, b, t) -> a |> fl t |> fold b |> ff h
          | BlockOC (b, t)    -> a |> fl t |> fold b
          | BNil              -> a
          | BMiddle n         -> a |> fm n
          | BCat (l, r)       -> a |> fold r |> fold l
          | BSnoc (b, n)      -> a |> fm n   |> fold b
          | BCons (n, b)      -> a |> fold b |> fm n in
      fold b a

  end
