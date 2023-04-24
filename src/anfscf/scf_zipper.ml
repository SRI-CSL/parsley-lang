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

(* Zipper data structure for the SCF IR. *)

open Parsing
open Anf
open Scf

(* The root structure is a block of instructions.  `zc` represents
   the context for the current location (or 'hole'). *)

(* Prefixes and suffixes of blocks and handlers: prefixes are in
   reverse order, while suffixes are in original order. *)
type bseg = bivalent_instr list
type hseg = linear_instr list

type bz = (* prefix *) bseg * (* suffix *) bseg
type hz = (* prefix *) hseg * (* suffix *) hseg

let zip_block ((p, s): bz) : sealed_block =
  seal_block ((List.rev s) @ p)

let zip_handler ((p, s): hz) : sealed_handler =
  seal_handler ((List.rev s) @ p)

type zctx =
  | Z_block of bz
  | Z_do of bz * exit_handler * Location.t * instr_id * zctx
  | Z_doh of sealed_block * handle * hz * Location.t * instr_id * zctx
  | Z_loop of bool * bz * Location.t * instr_id * zctx
  | Z_ift of av * bz * sealed_block * Location.t * instr_id * zctx
  | Z_ife of av * sealed_block * bz * Location.t * instr_id * zctx
  | Z_start_choices of
      frame_id * mutations FrameMap.t * bz * Location.t * instr_id * zctx

type scf_zipper = bivalent_instr * zctx

type error =
  | ZE_empty_block
  | ZE_empty_handler
  | ZE_empty_loop
  | ZE_no_loop_for_break
  | ZE_illegal_break_in_start_choices
  | ZE_illegal_break_in_handler_context
  | ZE_illegal_finish_choice
  | ZE_illegal_finish_choice_in_handler_context
  | ZE_illegal_continue_choice
  | ZE_illegal_continue_choice_no_choice
  | ZE_illegal_fail_choice
  | ZE_illegal_fail_choice_not_last
  | ZE_illegal_fail_in_start_choice
  | ZE_illegal_fail_in_handler

exception Error of Location.t * error

let error_msg = function
  | ZE_empty_block ->
      "unexpected empty block"
  | ZE_empty_handler ->
      "illegal empty handler"
  | ZE_empty_loop ->
      "illegal empty loop"
  | ZE_no_loop_for_break ->
      "no break found in loop"
  | ZE_illegal_break_in_start_choices ->
      "illegal break in start-choices"
  | ZE_illegal_break_in_handler_context ->
      "illegal break in handler context"
  | ZE_illegal_finish_choice ->
      "illegal finish-choice"
  | ZE_illegal_finish_choice_in_handler_context ->
      "illegal finish-choice in handler context"
  | ZE_illegal_continue_choice ->
      "illegal continue-choice"
  | ZE_illegal_continue_choice_no_choice ->
      "no choices left for continue-choice"
  | ZE_illegal_fail_choice ->
      "illegal fail-choice"
  | ZE_illegal_fail_choice_not_last ->
      "illegal fail-choice: choice is not last"
  | ZE_illegal_fail_in_start_choice ->
      "illegal fail-choice in start-choice"
  | ZE_illegal_fail_in_handler ->
      "illegal fail in handler"

let zipper_init (b: sealed_block) (l: Location.t) : scf_zipper =
  match unseal_block b with
    | []     -> raise (Error (l, ZE_empty_block))
    | h :: t -> h, Z_block ([], t)

(* Check whether the context is at the end of a block. *)

(* The zipper location is pointing at the instruction. *)
let last_in_block = function
  | Z_block (_, [_])
  | Z_do ((_, [_]), _, _, _, _)
  | Z_doh (_, _, (_, [_]), _, _, _)
  | Z_loop (_, (_, [_]), _, _, _)
  | Z_ift (_, (_, [_]), _, _, _, _)
  | Z_ife (_, _, (_, [_]), _, _, _)
  | Z_start_choices (_, _, (_, [_]), _, _, _) -> true
  | _                                         -> false

(* Step the context past the current instruction.  The resulting
   context may point at the end of a block, instead of the next
   instruction.  It does not cross block boundaries.  This is unlike
   `exec_next`, which always points to the next executed instruction,
   even it requires crossing block boundaries.
 *)
let step = function
  | Z_block (p, h :: t) -> Some (Z_block (h :: p, t))
  | Z_block (_, [])     -> None

  | Z_do ((p, h :: t), eh, l, i, z) -> Some (Z_do ((h :: p, t), eh, l, i, z))
  | Z_do ((_, []), _, _, _, _)      -> None

  | Z_doh (db, h, (p, hh :: ht), l, i, z) ->
      Some (Z_doh (db, h, (hh :: p, ht), l, i, z))
  | Z_doh (_, _, (_, []), _, _, _) ->
      None

  | Z_loop (f, (p, h :: t), l, i, z) ->
      Some (Z_loop (f, (h :: p, t), l, i, z))
  | Z_loop (_, (_, []), _, _, _) ->
      None

  | Z_ift (v, (p, h :: t), eb, l, i, z) ->
      Some (Z_ift (v, (h :: p, t), eb, l, i, z))
  | Z_ift (_, (_, []), _, _, _, _) ->
      None

  | Z_ife (v, tb, (p, h :: t), l, i, z) ->
      Some (Z_ife (v, tb, (h :: p, t), l, i, z))
  | Z_ife (_, _, (_, []), _, _, _) ->
      None

  | Z_start_choices (fid, muts, (p, h :: t), l, i, z) ->
      Some (Z_start_choices (fid, muts, (h :: p, t), l, i, z))
  | Z_start_choices (_, _, (_, []), _, _, _) ->
      None

(* Assuming the current instruction[*] succeeded, get next SCF
   instruction(s) in execution order (as opposed to traversal order)
   from the context; equivalently, get the first instruction in the
   success continuation.

   [*] This assumes that the current instruction is not one of the
       following explicit control flow instruction: `break`,
      `continue_choice`, `finish_choice`, and `fail`.
 *)

type exec_next =
  | EN_block of bivalent_instr
  | EN_handler of linear_instr
  | EN_done

let str_of_next = function
  | EN_block _   -> "block"
  | EN_handler _ -> "handler"
  | EN_done      -> "done"

let rec exec_next (z: zctx) : exec_next * zctx option =
  match z with
  | Z_block (p, h :: t) ->
      EN_block h, Some (Z_block (h :: p, t))
  | Z_block (_, []) ->
      EN_done, None
  | Z_do ((p, h :: t), eh, l, i, z) ->
      EN_block h, Some (Z_do ((h :: p, t), eh, l, i, z))
  | Z_do ((_, []), _, _, _, z) ->
      exec_next z
  | Z_doh (db, h, (p, hh :: ht), l, i, z) ->
      EN_handler hh, Some (Z_doh (db, h, (hh :: p, ht), l, i, z))
  | Z_doh (_, H_success, (_, []), _, _, z) ->
      exec_next z
  | Z_doh (_, H_failure, (_, []), _, _, z) ->
      fail_next z
  | Z_loop (f, (p, h :: t), l, i, z) ->
      EN_block h, Some (Z_loop (f, (h :: p, t), l, i, z))
  | Z_loop (f, (pre, []), l, i, z) ->
      (match List.rev pre with
         (* a loop should not be empty (since it should have at least
            a break or a matching instruction). *)
         | []     -> raise (Error (l, ZE_empty_loop))
         (* return to the top of the loop *)
         | h :: t -> EN_block h, Some (Z_loop (f, ([], t), l, i, z)))
  | Z_ift (v, (p, h :: t), eb, l, i, z) ->
      EN_block h, Some (Z_ift (v, (h :: p, t), eb, l, i, z))
  | Z_ift (_, (_, []), _, _, _, z) ->
      exec_next z
  | Z_ife (v, tb, (p, h :: t), l, i, z) ->
      EN_block h, Some (Z_ife (v, tb, (h :: p, t), l, i, z))
  | Z_ife (_, _, (_, []), _, _, z) ->
      exec_next z
  | Z_start_choices (fid, muts, (p, h :: t), l, i, z) ->
      EN_block h, Some (Z_start_choices (fid, muts, (h :: p, t), l, i, z))
  | Z_start_choices (_, _, (_, []), _, _, z) ->
      exec_next z

(* Get the first instruction in the closest enclosing handler;
   equivalently, get the first instruction in the failure
   continuation.

   This applies to any bivalent instruction other than `break`.
 *)
and fail_next (z: zctx) : exec_next * zctx option =
  match z with
    | Z_doh (db, h, ([], hh :: ht), l, i, z) ->
        EN_handler hh, Some (Z_doh (db, h, ([hh], ht), l, i, z))
    | Z_doh (_, H_failure, ([], []), l, _, _) ->
        raise (Error (l, ZE_empty_handler))
    | Z_doh (_, H_success, ([], []), _, _, z) ->
        exec_next z
    | Z_doh (_, _, (_ :: _, _), l, _, _) ->
        (* We should never fail in the middle of a handler. *)
        raise (Error (l, ZE_illegal_fail_in_handler))
    | Z_start_choices (_, _, (_, _::_), l, _, _) ->
        (* `fail` cannot exit out from the middle of `start_choices`;
           the only exits are `finish_choice` and `fail_choice`. *)
        raise (Error (l, ZE_illegal_fail_in_start_choice))
    | Z_start_choices (_, _, (_, []), _, _, z) ->
        (* We're failing out of the last choice, which is legal. *)
        fail_next z
    | Z_block _ ->
        EN_done, None
    | Z_do (bz, (h, hb), l, i, z) ->
        (match unseal_handler hb with
           | [] ->
               (* This can happen when we want to ignore failures. *)
               assert (h == H_success);
               exec_next z
           | hh :: ht ->
               let db = zip_block bz in
               let z = Z_doh (db, h, ([], ht), l, i, z) in
               EN_handler hh, Some z)
    | Z_loop (_, _, _, _, z) ->
        fail_next z
    | Z_ift (_, _, _, _, _, z) ->
        fail_next z
    | Z_ife (_, _, _, _, _, z) ->
        fail_next z

(* Specialized helpers for control flow. *)

let rec break_next (l: Location.t) (z: zctx) : exec_next * zctx option =
  (* It is an error not to encounter a loop. *)
  match z with
    | Z_block _ ->
        raise (Error (l, ZE_no_loop_for_break))
    | Z_doh _ ->
        raise (Error (l, ZE_illegal_break_in_handler_context))
    | Z_start_choices _ ->
        raise (Error (l, ZE_illegal_break_in_start_choices))
    | Z_loop (_, _, _, _, z) ->
        (* Execution continues after the loop. *)
        exec_next z
    | Z_do (_, _, _, _, z)
    | Z_ift (_, _, _, _, _, z)
    | Z_ife (_, _, _, _, _, z) ->
        break_next l z

let rec finish_choice_next (l: Location.t) (z: zctx)
        : exec_next * zctx option =
  match z with
    | Z_block _ ->
        raise (Error (l, ZE_illegal_finish_choice))
    | Z_doh _ ->
        raise (Error (l, ZE_illegal_finish_choice_in_handler_context))
    | Z_do (_, _, _, _, z)
    | Z_loop (_, _, _, _, z)
    | Z_ift (_, _, _, _, _, z)
    | Z_ife (_, _, _, _, _, z) ->
        finish_choice_next l z
    | Z_start_choices (_, _, _, _, _, z) ->
        (* Execution resumes after the `start_choices`. *)
        exec_next z

let rec continue_choice_next (l: Location.t) (z: zctx)
        : exec_next * zctx option =
  match z with
    | Z_block _ ->
        raise (Error (l, ZE_illegal_continue_choice))
    | Z_start_choices (_, _, (_, []), _, _, _) ->
        raise (Error (l, ZE_illegal_continue_choice_no_choice))
    | Z_start_choices (fid, muts, (p, h :: t), l, i, z) ->
        EN_block h, Some (Z_start_choices (fid, muts, (h :: p, t), l, i, z))
    | Z_doh (_, _, _, _, _, z)
    | Z_do (_, _, _, _, z)
    | Z_loop (_, _, _, _, z)
    | Z_ift (_, _, _, _, _, z)
    | Z_ife (_, _, _, _, _, z) ->
        continue_choice_next l z

let rec fail_choice_next (l: Location.t) (z: zctx)
        : exec_next * zctx option =
  match z with
    | Z_block _ ->
        raise (Error (l, ZE_illegal_fail_choice))
    | Z_start_choices (_, _, (_, _::_), _, _, _) ->
        raise (Error (l, ZE_illegal_fail_choice_not_last))
    | Z_start_choices (_, _, (_, []), _, _, z) ->
        (* Continue at the failure handler. *)
        fail_next z
    | Z_doh (_, _, _, _, _, z)
    | Z_do (_, _, _, _, z)
    | Z_loop (_, _, _, _, z)
    | Z_ift (_, _, _, _, _, z)
    | Z_ife (_, _, _, _, _, z) ->
        fail_choice_next l z
