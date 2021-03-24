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

module MkFactBase =
  functor (L: LATTICE) ->
  struct
    (* Lattice structure *)
    type f = L.t
    let bottom = L.bottom
    let join = L.join

    (* Factbases are maps from labels to facts in the lattice *)
    type factbase = f Label.LabelMap.t

    let get_fact fb l =
      match Label.LabelMap.find_opt l fb with
        | None   -> L.bottom
        | Some f -> f

    let lookup fb l =
      Label.LabelMap.find_opt l fb

    let add fb l f =
      Label.LabelMap.add l f fb

    let mk_factbase facts =
      List.fold_left (fun fb (l, f) ->
          add fb l (snd (L.join (get_fact fb l) f))
        ) Label.LabelMap.empty facts
  end

(* analysis passes (without rewrite transformations) *)

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

module MkAnalysis =
  functor (G: GRAPH) (FB: FACTBASE) ->
  struct
    module G     = G
    module FB    = FB

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

    let rec fwd_blk_transfer: type e x v.
                                   v fwd_transfer
                                   -> (e, x, v) G.Block.block
                                   -> e facts
                                   -> x facts =
      fun ((tr_co, tr_oo, tr_oc) as tr) b f ->
      match b with
        | BlockCO (h, b') ->
            f |> tr_co h |> fwd_blk_transfer tr b'
        | BlockOC (b', t) ->
            f |> fwd_blk_transfer tr b' |> tr_oc t
        | BlockCC (h, b', t) ->
            f |> tr_co h |> fwd_blk_transfer tr b' |> tr_oc t
        | BNil ->
            f
        | BMiddle n ->
            f |> tr_oo n
        | BCat (bl, br) ->
            f |> fwd_blk_transfer tr bl |> fwd_blk_transfer tr br
        | BSnoc (b', t) ->
            f |> fwd_blk_transfer tr b' |> tr_oo t
        | BCons (h, b') ->
            f |> tr_oo h |> fwd_blk_transfer tr b'

    (* The backward node transfer function by node shape. Note that
     * the backward transfer for a [(c, o) block] ends with a single
     * fact (i.e. an [o facts]) at the head node.  So the result fact
     * is always an [o facts]. *)
    type ('v) bwd_transfer =
      ( ((c, o, 'v) G.Block.node -> o facts -> o facts)
      * ((o, o, 'v) G.Block.node -> o facts -> o facts)
      * ((o, c, 'v) G.Block.node -> c facts -> o facts)
      )
(*
    let rec bwd_blk_transfer: type e x v.
                                   v bwd_transfer
                                   -> (e, x, v) G.Block.block
                                   -> x facts
                                   -> o facts =
      fun ((tr_co, tr_oo, tr_oc) as tr) b f ->
      match b with
        | BlockCO (h, b') ->
            f |> bwd_blk_transfer tr b' |> tr_co h
        | BlockOC (b', t) ->
            f |> tr_oc t |> bwd_blk_transfer tr b'
        | BlockCC (h, b', t) ->
            f |> tr_oc t |> bwd_blk_transfer tr b' |> tr_co h
        | BNil ->
            f
        | BMiddle n ->
            f |> tr_oo n
        | BCat (bl, br) ->
            f |> bwd_blk_transfer tr br |> bwd_blk_transfer tr bl
        | BSnoc (b', t) ->
            f |> tr_oo t |> bwd_blk_transfer tr b'
        | BCons (h, b') ->
            f |> bwd_blk_transfer tr b' |> tr_oo h
 *)
    module IntMap   = Map.Make(Int)
    module IntSet   = Set.Make(Int)
    module LabelMap = Label.LabelMap

    (* internal convenience types *)
    type 'v closed = (c, c, 'v) G.Block.block
    type ('v) blk_transfer =
      (c, c, 'v) G.Block.block -> FB.factbase -> FB.factbase

    (* internal converter *)
    let mk_fwd_blk_transfer (type v) (tr: v fwd_transfer) : v blk_transfer =
      fun (b: (c, c, v) G.Block.block) (fb: FB.factbase) ->
      match fwd_blk_transfer tr b (Facts_closed fb) with
        | Facts_closed fb -> fb
        | Facts_open _ -> assert false (* this should not be needed *)

    (* Orders the blocks into the order best suited for the direction
     * of analysis.  This returns an ordered integer map to these
     * ordered blocks, such that the keys of the map can be used in an
     * ordered todo worklist. *)
    let order_and_map dir entry blockmap =
      let dep_order dir entry blockmap =
        let order = G.rev_postorder blockmap entry in
        match dir with
          | Forward  -> order
          | Backward -> List.rev order in
      let blocks = dep_order dir entry blockmap in
      let idx_map = List.fold_left (fun (idx, m) b ->
                        let m = IntMap.add idx b m in
                        (idx + 1, m)
                      ) (0, IntMap.empty) blocks in
      blocks, snd idx_map

    (* Computes a map from a label to the indices of the blocks whose
     * facts would need re-computed when the fact at the label
     * changes. The [blocks] argument should be in the order used to
     * compute the dependency map.
     *)
    let compute_dependencies dir (blocks: 'v closed list)
        : IntSet.t LabelMap.t =
      match dir with
        | Forward ->
            snd (List.fold_left (fun (idx, m) b ->
                     let l = G.Block.entry_label b in
                     let d = IntSet.singleton idx in
                     idx + 1, LabelMap.add l d m
                   ) (0, LabelMap.empty) blocks)
        | Backward ->
            snd (List.fold_left (fun (idx, m) b ->
                     let m =
                       List.fold_left (fun m s ->
                           match LabelMap.find_opt s m with
                             | Some d ->
                                 LabelMap.add s (IntSet.add idx d) m
                             | None ->
                                 LabelMap.add s (IntSet.singleton idx) m
                         ) m (G.Block.successors b) in
                     idx + 1, m
                   ) (0, LabelMap.empty) blocks)

    (* Update todo and factbase from the output of a block transfer. *)
    let update (deps: IntSet.t LabelMap.t) (l: Label.label) (f: FB.f)
          (todo, fbase) =
      let updated_todo () =
        match LabelMap.find_opt l deps with
          | None   -> todo
          | Some d -> IntSet.union d todo in
      match FB.lookup fbase l with
        | None ->
            updated_todo (), FB.add fbase l f
        | Some f' ->
            (match FB.join f' f with
               | NoChange, _    -> todo, fbase
               | SomeChange, f' -> updated_todo (), FB.add fbase l f')

    (* Fixpoint routine parameterized over analysis direction.  It is
     * an error to give an empty list of entry points.
     *)
    let fixpoint_analysis
          (type v)
          (dir: direction)
          (entries: Label.label list)
          (blockmap: (v closed) LabelMap.t)
          (init_fbase: FB.factbase)
          (transfer: v blk_transfer)
        : FB.factbase =
      (* adjust the algorithm state for the special case of an empty
       * [entries], which is (arbitrarily?) defined as a nop *)
      let todo, idx_map, dep_map =
        match entries with
          | [] ->
              (* if no entries are provided, the fixpoint is a no-op *)
              IntSet.empty, IntMap.empty, LabelMap.empty
          | entry :: _ ->
              (* use any entry to compute the appropriate block
               * ordering and an indexed map *)
              let ord_blocks, idx_map =
                order_and_map dir entry blockmap in
              (* compute the dependency map *)
              let dep_map = compute_dependencies dir ord_blocks in
              (* add all blocks (via their indices) to the todo list *)
              let todo =
                List.fold_left (fun s (k, _) ->
                    IntSet.add k s
                  ) IntSet.empty (IntMap.bindings idx_map) in
              todo, idx_map, dep_map in
      (* choose the earliest in dep order from the todo list *)
      let choose todo =
        match IntSet.min_elt_opt todo with
          | None   -> None
          | Some i -> Some (i, IntSet.remove i todo) in
      (* loop over todo until empty to get fixpoint of fbase *)
      let rec loop todo fbase =
        match choose todo with
          | None ->
              fbase
          | Some (i, todo) ->
              let blk = IntMap.find i idx_map in
              let out_facts = transfer blk fbase in
              (* update fbase and todo list *)
              let todo, fbase =
                LabelMap.fold (update dep_map) out_facts (todo, fbase) in
              loop todo fbase in
      loop todo init_fbase

    (* Forward dataflow analysis that takes a list of entry points
     * for graphs that are closed at entry, and returns the facts at
     * the graph exit(s), along with any facts for the body *)
    let fwd_analysis (type e x v)
          (init_facts: e facts)
          (entries: (e, Label.label list) maybeC)
          (g: (e, x, v) G.graph)
          (tr: v fwd_transfer)
        : x facts * FB.factbase option
      =
      (* If there is any prologue, get the factbase at its exit.
       * Handle open graphs at the end. *)
      let transfer_prologue (type e v)
            (b: (e, (o, c, v) G.Block.block) maybeO)
            (init: e facts)
            (tr: v fwd_transfer)
          : c facts =
        match init, b with
          | Facts_open f, JustO b ->
              fwd_blk_transfer tr b (Facts_open f)
          | Facts_closed fb, NothingO ->
              Facts_closed fb
          (* this should not be needed *)
          | _ -> assert false in
      let prologue_exit, entries =
        match init_facts, g, entries with
          | _, GNil, _ | _,  GUnit _, _ ->
              None, None
          | Facts_open _,    GMany (JustO p, _, _), NothingC ->
              Some (transfer_prologue (JustO p) init_facts tr),
              Some (G.Block.successors p)
          | Facts_closed fb, GMany (NothingO, _, _), JustC e ->
              Some (Facts_closed fb), Some e
          | Facts_open _,    GMany (JustO _, _, _), JustC _
          | Facts_open _,    GMany (NothingO, _, _), _
          | Facts_closed _,  GMany (JustO _, _, _), _
          | Facts_closed _,  GMany (NothingO, _, _), NothingC ->
              (* this should never happen *)
              assert false in

      (* compute the factbase at the end of the body, if any *)
      let body_fb =
        match prologue_exit, entries, g with
          | Some (Facts_closed fb), Some es, GMany (_, body, _) ->
              let tr = mk_fwd_blk_transfer tr in
              let fb = fixpoint_analysis Forward es body fb tr in
              Some fb
          | None, _, GNil | None, _, GUnit _ ->
              None
          | _, _, _ ->
              (* should never come here *)
              assert false in

      (* compute the final factbase; handle any open graphs here *)
      match init_facts, body_fb, g with
        | Facts_open f, None,    GNil ->
            Facts_open f, None
        | Facts_open f, None,    GUnit b ->
            fwd_blk_transfer tr b (Facts_open f), None
        | _,            Some fb, GMany (_, _, NothingO) ->
            Facts_closed fb, Some fb
        | _,            Some fb, GMany (_, _, JustO b) ->
            fwd_blk_transfer tr b (Facts_closed fb), Some fb
        | _, _, _ ->
            (* should never come here *)
            assert false
  end
