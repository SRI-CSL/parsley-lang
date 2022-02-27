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
   The target block generalizes as slightly well: it can consist only
   of a `jump` or `fail` node.

   This also generalizes to a sequence of jumps where the intermediate
   jump blocks are trivial.
 *)

(* Trivial jump blocks consist of a single jump/fail node. *)
let is_jmp_block (b: closed) : bool =
  let _, b = B.split_head b in
  let b, x = B.split_tail b in
  let exit_is_jmp = match x with
      | Node.N_jump _
      | Node.N_fail _ -> true
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
  {info_entries:  string LabelMap.t;
   info_rev_map:  LabelSet.t LabelMap.t;
   info_jmp_blks: closed LabelMap.t}

let analyze (spec: spec_ir) : info =
  let blocks = spec.ir_blocks in
  let info_rev_map, info_jmp_blks =
    LabelMap.fold (fun l b (m, s) ->
        assert (l = B.entry_label b);
        List.fold_left (fun m t ->
            (* `t` is a raw label, and could correspond to either a
               static or dynamic label.  If it is static, there should
               be a corresponding block `b'` in `blocks`.  If `b` is
               optimized out, `b'` would need to be adjusted.  If `t`
               is dynamic, it doesn't correspond to a block, and can
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
    FormatGToC.fold (fun nt ent m ->
        let entry = ent.nt_entry in
        LabelMap.add entry nt m
      ) spec.ir_gtoc LabelMap.empty in
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
  (* This relies on the implementation detail that the dynamic and
     static labels share the underlying raw label space; i.e. that
     static and dynamic labels can never have aliased raw labels. *)
  let rl = raw_label_of l in
  match LabelMap.find_opt rl map with
    | None   -> l
    | Some t -> if   is_static l
                then L_static  t
                else L_dynamic t

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
    | N_fail (l, t) ->
        let t = retarget_label map t in
        N_fail (l, t)
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
    | N_call_nonterm (nt, ps, r, ls, lf) ->
        let ls = retarget_label map ls in
        let lf = retarget_label map lf in
        N_call_nonterm (nt, ps, r, ls, lf)
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

let optimize (spec: spec_ir) (debug: bool) : spec_ir =
  let info = analyze spec in
  let blocks = spec.ir_blocks in
  (* Entries in the reverse map cannot exceed the total number of
     blocks.  This assertion can catch erroneous entries for dynamic
     labels. *)
  assert (LabelMap.cardinal info.info_rev_map <= LabelMap.cardinal blocks);
  let ir_blocks = optimize_blocks info blocks in
  if   debug
  then Printf.printf "Optimized (removed) %d trivial jump blocks.\n"
         ((LabelMap.cardinal blocks) - (LabelMap.cardinal ir_blocks));
  {spec with ir_blocks}

(* A routine to do some sanity checks on the IR for a spec.  It checks
   for the following:

   . The entry label for each non-terminal should correspond to a
     defined block, and its success and failure continuations should
     be dynamic.

   . Each non-terminal should have a unique entry block.

   . All static labels of all exit nodes in the IR should point to
     defined blocks, and dynamic labels should be known.

   . Entry blocks for non-terminals should not have static callers
     (since their invocation is dynamic).  Similarly, blocks with
     static callers should not be entry blocks.

   These invariants should hold pre- and post- optimization.

   In addition, for an optimized IR:

   . There should be no trivial jump blocks.

   . All blocks in the IR should have at least one caller block or be
     an entry block for a non-terminal (or both).  That is, there
     should be no unused (or 'garbage') blocks.
 *)

let validate (spec: spec_ir) (optimized: bool) (debug: bool) : unit =
  let info = analyze spec in
  (* An optimized IR should not contain jump blocks. *)
  if   optimized
  then assert (LabelMap.cardinal info.info_jmp_blks = 0);
  (* Construct the set of known dynamic labels. *)
  let _, dyn_labels =
    FormatGToC.fold (fun nt ent (em, dls) ->
        (* The continuations should be dynamic. *)
        assert (is_dynamic ent.nt_succcont);
        assert (is_dynamic ent.nt_failcont);
        (* They should also be unique. *)
        let ls = raw_label_of ent.nt_succcont in
        let lf = raw_label_of ent.nt_failcont in
        assert (not (LabelSet.mem ls dls));
        assert (not (LabelSet.mem lf dls));
        (* Each non-terminal should have a unique entry block. *)
        let entry = ent.nt_entry in
        assert (not (LabelMap.mem entry em));
        (* The entry block should be defined. *)
        assert (LabelMap.mem entry spec.ir_blocks);
        (* It should have been found by the analysis. *)
        assert (LabelMap.find entry info.info_entries = nt);
        (* Update info. *)
        let em  = LabelMap.add entry nt em in
        let dls = LabelSet.add ls dls in
        let dls = LabelSet.add lf dls in
        em, dls
      ) spec.ir_gtoc (LabelMap.empty, LabelSet.empty) in
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
         should go to defined blocks and dynamic labels should be
         known.  Since `successors` doesn't tell us whether a label
         is static or dynamic, we can check that one of these
         properties holds, but we can't tell whether the right
         property holds. *)
      let succs = B.successors b in
      List.iter (fun l ->
          let is_known_dynamic  = LabelSet.mem l dyn_labels in
          let is_defined_static = LabelMap.mem l spec.ir_blocks in
          assert (is_known_dynamic || is_defined_static)
        ) succs;
    ) spec.ir_blocks;
  (* It is possible for unoptimized IR to have garbage (i.e. unused)
     blocks. For e.g., 'pure' non-terminals with only action elements
     and no parsing actions can generated unused cleanup blocks.
     Similarly, choice combinators whose last (typically default)
     choice can never fail creates an unused failure trampoline.  But
     optimized IR should remove all these blocks. *)
  if   optimized
  then assert (not !have_garbage)
