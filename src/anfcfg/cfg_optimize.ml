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

open Flow
open Anf_common
open Cfg

(* IR simplification and validation. *)

module LabelSet = Set.Make(LabelOrdSet)
module LabelMap = Map.Make(LabelOrdSet)

(* Jump simplification.  Jumps (`jmp l`) in source blocks to
   target blocks `l` that consist entirely of another jump (`jmp
   l'`) to yet another (static, target) block `l'` can be replaced in
   the source block by `jmp l'` to the final target block, and the
   intermediate "trivial" target block `l` can be removed.

   This generalizes to other source control-transfer instructions.
   This also generalizes to a sequence of jumps where the intermediate
   jump blocks are trivial.
 *)

(* Trivial jump blocks consist of a single jump node. *)
let is_jmp_block (b: closed) : bool =
  let _, b = B.split_head b in
  let b, x = B.split_tail b in
  let exit_is_jmp = match x with
      | Node.N_jump _ -> true
      | _             -> false in
  let is_trivial = match B.to_list b with
      | [] -> true
      | _  -> false in
  is_trivial && exit_is_jmp

(* The information computed by analysis:
   . the entry blocks for each non-terminal
   . the set of callers for each block
   . the set of trivial jump blocks
 *)
type info =
  {info_entries:  (modul * string) LabelMap.t;
   info_rev_map:  LabelSet.t LabelMap.t;
   info_jmp_blks: closed LabelMap.t}

let analyze (spec: spec_cfg) : info =
  let blocks = spec.cfg_blocks in
  let info_rev_map, info_jmp_blks =
    LabelMap.fold (fun l b (m, s) ->
        assert (l = B.entry_label b);
        List.fold_left (fun m t ->
            (* `t` is a raw label, and could correspond to either a
               static or virtual label.  If it is static, there should
               be a corresponding block `b'` in `blocks`.  If `b` is
               optimized out, `b'` would need to be adjusted.  If `t`
               is virtual, it doesn't correspond to a block, and can
               be ignored.  *)
            match LabelMap.find_opt t blocks with
              | None   -> m
              | Some _ -> let srcs =
                            match LabelMap.find_opt t m with
                              | Some srcs -> LabelSet.add l srcs
                              | None      -> LabelSet.singleton l in
                          LabelMap.add t srcs m
          ) m (B.successors b),
        if   is_jmp_block b
        then LabelMap.add l b s
        else s
      ) blocks (LabelMap.empty, LabelMap.empty) in
  let info_entries =
    ValueMap.fold (fun nt ent m ->
        let entry = ent.nt_entry in
        LabelMap.add entry nt m
      ) spec.cfg_gtoc LabelMap.empty in
  {info_entries;
   info_rev_map;
   info_jmp_blks}

(* Compute the target of a jump block. *)
let target (info: info) (jb: closed) : Label.label =
  assert (is_jmp_block jb);
  let rec follow jb trail =
    let successors = B.successors jb in
    assert (List.length successors = 1);
    let t = List.hd successors in
    (* If the target is another jump block, then follow it to the
       final target, otherwise this is the final target.  We should
       never get into an infinite loop; the assert using `trail`
       ensures that. *)
    assert (not (LabelSet.mem t trail));
    match LabelMap.find_opt t info.info_jmp_blks with
      | None     -> t
      | Some jb' -> follow jb' (LabelSet.add t trail) in
  follow jb LabelSet.empty

(* Build the target map for each jump block. *)
let build_target_map (info: info) : Label.label LabelMap.t =
  LabelMap.fold (fun l jb m ->
      assert (l = B.entry_label jb);
      assert (is_jmp_block jb);
      let tgt = target info jb in
      assert (not (LabelMap.mem l m));
      LabelMap.add l tgt m
    ) info.info_jmp_blks LabelMap.empty

(* Target rewriting. *)

let retarget_label (map: Label.label LabelMap.t) (l: label)
    : label =
  (* This relies on the implementation detail that the virtual and
     static labels share the underlying raw label space; i.e. that
     static and virtual labels can never have aliased raw labels. *)
  let rl = raw_label_of l in
  match LabelMap.find_opt rl map with
    | None   -> l
    | Some t -> if   is_static l
                then L_static  t
                else L_virtual t

let retarget_exit (map: Label.label LabelMap.t) (nd: Node.exit_node)
    : Node.exit_node =
  match nd with
    | N_bits (l, w, ls, lf) ->
        let ls = retarget_label map ls in
        let lf = retarget_label map lf in
        N_bits (l, w, ls, lf)
    | N_align (l, w, ls, lf) ->
        let ls = retarget_label map ls in
        let lf = retarget_label map lf in
        N_align (l, w, ls, lf)
    | N_pad (l, w, ls, lf) ->
        let ls = retarget_label map ls in
        let lf = retarget_label map lf in
        N_pad (l, w, ls, lf)
    | N_collect_checked_bits (l, v, p, ls, lf) ->
        let ls = retarget_label map ls in
        let lf = retarget_label map lf in
        N_collect_checked_bits (l, v, p, ls, lf)
    | N_check_bits (l, p, ls, lf) ->
        let ls = retarget_label map ls in
        let lf = retarget_label map lf in
        N_check_bits (l, p, ls, lf)
    | N_jump (l, t) ->
        let t = retarget_label map t in
        N_jump (l, t)
    | N_return (l, t) ->
        let t = retarget_label map t in
        N_return (l, t)
    | N_constraint (l, v, ls, lf) ->
        let ls = retarget_label map ls in
        let lf = retarget_label map lf in
        N_constraint (l, v, ls, lf)
    | N_cond_branch (l, v, ls, lf) ->
        let ls = retarget_label map ls in
        let lf = retarget_label map lf in
        N_cond_branch (l, v, ls, lf)
    | N_exec_dfa (dfa, v, ls, lf) ->
        let ls = retarget_label map ls in
        let lf = retarget_label map lf in
        N_exec_dfa (dfa, v, ls, lf)
    | N_scan (l, s, v, ls, lf) ->
        let ls = retarget_label map ls in
        let lf = retarget_label map lf in
        N_scan (l, s, v, ls, lf)
    | N_call_nonterm (m, nt, ps, r, ls, lf) ->
        let ls = retarget_label map ls in
        let lf = retarget_label map lf in
        N_call_nonterm (m, nt, ps, r, ls, lf)
    | N_require_remaining (v, n, lb, lc) ->
        let lb = retarget_label map lb in
        let lc = retarget_label map lc in
        N_require_remaining (v, n, lb, lc)
    (* this should not be needed *)
    | _ ->
        assert false

let retarget_block (map: Label.label LabelMap.t) (b: closed)
    : closed =
  let e, b = B.split_head b in
  let b, x = B.split_tail b in
  let x = retarget_exit map x in
  let b = B.join_tail b x in
  B.join_head e b

(* Jump optimization pass. *)
let optimize_blocks (info: info) (blocks: closed LabelMap.t) :
      closed LabelMap.t =
  let target_map = build_target_map info in
  LabelMap.fold (fun l b m ->
      assert (l = B.entry_label b);
      (* This block is in use if it has a caller or if it is an entry
         block. *)
      let is_entry   = LabelMap.mem l info.info_entries in
      let has_caller =
        match LabelMap.find_opt l info.info_rev_map with
          | None   -> false
          | Some _ -> true in
      let is_in_use = is_entry || has_caller in
      if   LabelMap.mem l info.info_jmp_blks
      then ( (* Every jump block should have a caller. *)
             assert (LabelMap.mem l info.info_rev_map);
             (* Drop the jump block in the optimized IR. *)
             m )
      else if not is_in_use
      then m (* Drop unused blocks. *)
      else let b = retarget_block target_map b in
           LabelMap.add l b m
    ) blocks LabelMap.empty

let optimize (spec: spec_cfg) (debug: bool) : spec_cfg =
  let info = analyze spec in
  let blocks = spec.cfg_blocks in
  (* Entries in the reverse map cannot exceed the total number of
     blocks.  This assertion can catch erroneous entries for virtual
     labels. *)
  assert (LabelMap.cardinal info.info_rev_map <= LabelMap.cardinal blocks);
  let cfg_blocks = optimize_blocks info blocks in
  if   debug
  then Printf.printf "Optimized (removed) %d trivial jump blocks.\n"
         ((LabelMap.cardinal blocks) - (LabelMap.cardinal cfg_blocks));
  {spec with cfg_blocks}

(* Back-pointer insertion pass.

   It is fragile and complex to keep and update back-pointers to
   predecessor blocks during CFG construction and optimization.  So
   each block is created with an empty set of predecessor blocks.  For
   simplicity, the back-pointers are created after the CFG is fully
   constructed and optimized.

   After this pass, the CFG should satisfy:

   . soundness: for each back-label `l` in the entry node of any block
     `b`, if `l` points to a block `b'`, then `b'` has an exit node
     containing `l` as a successor.

   . completeness: for each `l` label in the exit node of a block `b`,
     if `l` points to a block `b'`, then `l` should be a back-label of
     the entry node of `b'`.

   The block existence check is required, since virtual labels
   appearing in exit nodes do not point to blocks.
 *)

let predecessors (b: closed) : LabelSet.t =
  let e, _ = B.split_head b in
  match e with
    | Node.N_label (_, _, s) -> s
    | _                      -> assert false

let connect_predecessors (spec: spec_cfg) : spec_cfg =
  let info = analyze spec in
  let blocks = LabelMap.fold (fun l b m ->
                   let b =
                     match LabelMap.find_opt l info.info_rev_map with
                       | None    -> b
                       | Some ps ->
                           (* Fix up predecessors in the entry node. *)
                           let e, t = B.split_head b in
                           let e = match e with
                               | Node.N_label (loc, l', s) ->
                                   assert (l = l');
                                   assert (LabelSet.is_empty s);
                                   Node.N_label (loc, l, ps)
                               | _ -> assert false in
                           B.join_head e t in
                   LabelMap.add l b m
                 ) spec.cfg_blocks LabelMap.empty in
  {spec with cfg_blocks = blocks}

(* A routine to do some sanity checks on the IR for a spec.  It checks
   for the following:

   . The entry label for each non-terminal should correspond to a
     defined block, and its success and failure continuations should
     be virtual.

   . Each non-terminal should have a unique entry block.

   . All static labels of all exit nodes in the IR should point to
     defined blocks, and virtual labels should be known.

   . Entry blocks for non-terminals should not have static callers
     (since their invocation is virtual).  Similarly, blocks with
     static callers should not be entry blocks.

   These invariants should hold pre- and post- optimization.

   In addition, for an optimized IR:

   . There should be no trivial jump blocks.

   . All blocks in the IR should have at least one caller block or be
     an entry block for a non-terminal (or both).  That is, there
     should be no unused (or 'garbage') blocks.
 *)

let validate (spec: spec_cfg) (optimized: bool) (debug: bool) : unit =
  let info = analyze spec in
  (* An optimized IR should not contain jump blocks. *)
  if   optimized
  then assert (LabelMap.cardinal info.info_jmp_blks = 0);
  (* Construct the set of known virtual labels. *)
  let _, dyn_labels =
    ValueMap.fold (fun nt ent (em, dls) ->
        (* The continuations should be virtual. *)
        assert (is_virtual ent.nt_succcont);
        assert (is_virtual ent.nt_failcont);
        (* They should also be unique. *)
        let ls = raw_label_of ent.nt_succcont in
        let lf = raw_label_of ent.nt_failcont in
        assert (not (LabelSet.mem ls dls));
        assert (not (LabelSet.mem lf dls));
        (* Each non-terminal should have a unique entry block. *)
        let entry = ent.nt_entry in
        assert (not (LabelMap.mem entry em));
        (* The entry block should be defined. *)
        assert (LabelMap.mem entry spec.cfg_blocks);
        (* It should have been found by the analysis. *)
        assert (LabelMap.find entry info.info_entries = nt);
        (* Update info. *)
        let em  = LabelMap.add entry nt em in
        let dls = LabelSet.add ls dls in
        let dls = LabelSet.add lf dls in
        em, dls
      ) spec.cfg_gtoc (LabelMap.empty, LabelSet.empty) in
  let have_garbage = ref false in
  (* Per-block invariants. *)
  LabelMap.iter (fun l b ->
      let has_caller =
        match LabelMap.find_opt l info.info_rev_map with
          | None    -> false
          | Some cs -> (assert (not (LabelSet.is_empty cs));
                        true) in
      let is_entry = LabelMap.mem l info.info_entries in
      (* check if `b` is relevant, i.e. not an unused block. *)
      (if   not (is_entry || has_caller)
       then (if   debug
             then Printf.printf "Block %s seems to be unused.\n"
                    (Label.to_string l);
             have_garbage := true)
       else (* Entry blocks should not have callers; called blocks
               should not be entry blocks. *)
            assert (   (is_entry && not has_caller)
                    || (not is_entry && has_caller)));
      (* Exits from `b` should be well-defined; i.e. static labels
         should go to defined blocks and virtual labels should be
         known.  Since `successors` doesn't tell us whether a label
         is static or virtual, we can check that one of these
         properties holds, but we can't tell whether the right
         property holds. *)
      List.iter (fun s ->
          let is_known_virtual  = LabelSet.mem s dyn_labels in
          let is_defined_static = LabelMap.mem s spec.cfg_blocks in
          assert (is_known_virtual || is_defined_static);
          assert (not (is_known_virtual && is_defined_static));
          (* Check predecessor completeness when optimized *)
          if   is_defined_static && optimized
          then let b' = LabelMap.find s spec.cfg_blocks in
               assert (LabelSet.mem l (predecessors b'))
        ) (B.successors b);
      (* Check predecessor soundness when optimized *)
      if   optimized
      then LabelSet.iter (fun p ->
               match LabelMap.find_opt p spec.cfg_blocks with
                 | None    -> assert false
                 | Some b' -> assert (List.mem l (B.successors b'))
             ) (predecessors b)
    ) spec.cfg_blocks;
  (* It is possible for unoptimized IR to have garbage (i.e. unused)
     blocks. For e.g., 'pure' non-terminals with only action elements
     and no parsing actions can generated unused cleanup blocks.
     Similarly, choice combinators whose last (typically default)
     choice can never fail creates an unused failure trampoline.  But
     optimized IR should remove all these blocks. *)
  if   optimized
  then assert (not !have_garbage)
