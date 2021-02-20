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

module type BLOCK =
  sig
    type ('e, 'x, 'v) node

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

    val empty: (o, o, 'v) block

    (* a block is empty if it does not contain any nodes *)
    val is_empty: ('e, 'x, 'v) block -> bool

    val entry_label: (c, 'x, 'v) block  -> Label.label
    val successors: ('e, c, 'v) block -> Label.label list

    (* construction *)

    val cons: (o, o, 'v)  node  -> (o, 'x, 'v) block -> (o, 'x, 'v) block
    val snoc: ('e, o, 'v) block -> (o, o, 'v)  node  -> ('e, o, 'v) block

    val join: (c, o, 'v)  node  -> (o, o, 'v) block  -> (o, c, 'v) node -> (c, c, 'v) block

    val join_head: (c, o, 'v)  node  -> (o, 'x, 'v) block -> (c, 'x, 'v) block
    val join_tail: ('e, o, 'v) block -> (o, c, 'v)  node  -> ('e, c, 'v) block

    val join_any: ('e, (c, o, 'v) node) maybeC -> (o, o, 'v) block -> ('x, (o, c, 'v) node) maybeC
                  -> ('e, 'x, 'v) block
    val append: ('e, o, 'v) block -> (o, 'x, 'v) block -> ('e, 'x, 'v) block

    (* deconstruction *)

    val first_node: (c, 'x, 'v) block -> (c, o, 'v) node
    val last_node:  ('e, c, 'v) block -> (o, c, 'v) node
    val end_nodes:  (c, c, 'v)  block -> (c, o, 'v) node * (o, c, 'v) node

    val split_head: (c, 'x, 'v) block -> (c, o, 'v)  node  * (o, 'x, 'v) block
    val split_tail: ('e, c, 'v) block -> ('e, o, 'v) block * (o, c, 'v)  node

    val split: (c, c, 'v) block -> (c, o, 'v) node * (o, o, 'v) block * (o, c, 'v) node

    val split_any: ('e, 'x, 'v) block ->
                   ('e, (c, o, 'v) node) maybeC * (o, o, 'v) block * ('x, (o, c, 'v) node) maybeC

    (* conversions *)

    val to_list: (o, o, 'v) block -> (o, o, 'v) node list
    val from_list: (o, o, 'v) node list -> (o, o, 'v) block

    (* modification *)

    val replace_first_node: (c, 'x, 'v) block -> (c, o, 'v) node -> (c, 'x, 'v) block
    val replace_last_node:  ('e, c, 'v) block -> (o, c, 'v) node -> ('e, c, 'v) block

    (* mapping *)

    val map: ( ((c, o, 'v) node -> (c, o, 'w) node)
             * ((o, o, 'v) node -> (o, o, 'w) node)
             * ((o, c, 'v) node -> (o, c, 'w) node) )
             -> ('e, 'x, 'v)  block
             -> ('e, 'x, 'w) block

    (* folding forward and backward *)

    val ffold: ( ((c, o, 'v) node -> 'a -> 'a)
               * ((o, o, 'v) node -> 'a -> 'a)
               * ((o, c, 'v) node -> 'a -> 'a) )
               -> ('e, 'x, 'v) block -> 'a -> 'a

    val bfold: ( ((c, o, 'v) node -> 'a -> 'a)
               * ((o, o, 'v) node -> 'a -> 'a)
               * ((o, c, 'v) node -> 'a -> 'a) )
               -> ('e, 'x, 'v) block -> 'a -> 'a
  end

module MkBlock (N: NODE) : BLOCK
       with type ('e, 'x, 'v) node = ('e, 'x, 'v) N.node
