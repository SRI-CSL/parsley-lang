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

(* Context/continuation data structure for the SCF IR, implemented as
   a zipper.

   The context is paired with a 'current' instruction in the
   interpreter; the invariant maintained is that the context is
   pointing at the _next_ instruction in the block in which the
   current instruction occurs.  If the current instruction is the last
   instruction in the block, the context points to an empty block.

 *)

open Parsing
open Anfscf
open Anf
open Scf

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

type zscf =
  | Zscf_root of sealed_block
  | Zscf_assign_var of var * zscf
  | Zscf_block of bz * zscf
  | Zscf_do of bz * exit_handler * zscf
  | Zscf_doh of sealed_block * handle * hz * zscf
  | Zscf_loop of bool * bz * zscf
  | Zscf_ift of av * bz * sealed_block * zscf
  | Zscf_ife of av * sealed_block * bz * zscf
  | Zscf_start_choices of frame_id * mutations FrameMap.t * bz * zscf

(* Create the initial continuation from a non-terminal code block. *)
let init_zscf (sb: sealed_block) : zscf =
  let root = Zscf_root sb in
  let b = unseal_block sb in
  Zscf_block (([], b), root)

let is_done z =
  match z with
    | Zscf_root _ -> true
    | _           -> false

(* Check whether the context is at the end of a block.  Note that the
   zipper location is pointing _past_ the current instruction, but not
   necessarily _at_ the next instruction. *)
let last_in_block = function
  | Zscf_block ((_, []), _)
  | Zscf_do ((_, []), _, _)
  | Zscf_doh (_, _, (_, []), _)
  | Zscf_loop (_, (_, []), _)
  | Zscf_ift (_, (_, []), _, _)
  | Zscf_ife (_, _, (_, []), _)
  | Zscf_start_choices (_, _, (_, []), _) -> true
  | _                                     -> false

let in_handler_block = function
  | Zscf_doh _ -> true
  | _          -> false

(* Print the frame of the context. *)
let str_of_top_zscf z =
  match z with
    | Zscf_root _ ->
        "[root]"
    | Zscf_assign_var (v, _) ->
        Printf.sprintf "[%s := ]" (Anf_printer.string_of_var v)
    | Zscf_block _ ->
        "[block]"
    | Zscf_do _ ->
        "[do]"
    | Zscf_doh _ ->
        "[do handler]"
    | Zscf_loop _ ->
        "[loop]"
    | Zscf_ift (av, _, _, _) ->
        Printf.sprintf "[if %s then]" (Anf_printer.string_of_av av)
    | Zscf_ife (av, _, _, _) ->
        Printf.sprintf "[if %s else]" (Anf_printer.string_of_av av)
    | Zscf_start_choices _ ->
        "[choices]"

(* These errors should have been caught by the SCF validator.*)
type error =
  | ZE_no_loop_for_break
  | ZE_illegal_next_in_assign_var
  | ZE_illegal_break_in_assign_var
  | ZE_illegal_break_in_start_choices
  | ZE_illegal_break_in_handler
  | ZE_illegal_finish_choice
  | ZE_illegal_finish_choice_in_assign_var
  | ZE_illegal_finish_choice_in_handler
  | ZE_illegal_finish_choice_in_loop
  | ZE_illegal_continue_choice
  | ZE_illegal_continue_choice_in_assign_var
  | ZE_illegal_continue_choice_in_loop
  | ZE_illegal_continue_choice_in_handler
  | ZE_illegal_continue_choice_in_failing_handler
  | ZE_illegal_fail_choice
  | ZE_illegal_fail_choice_in_assign_var
  | ZE_illegal_fail_choice_in_loop
  | ZE_illegal_fail_choice_in_handler
  | ZE_illegal_fail_choice_in_success_handler
  | ZE_illegal_fail_in_assign_var
  | ZE_illegal_fail_in_start_choice
  | ZE_illegal_fail_in_handler

exception Error of Location.t * error

let exn_msg = function
  | ZE_no_loop_for_break ->
      "no break found in loop"
  | ZE_illegal_next_in_assign_var ->
      "illegal next when awaiting assignment"
  | ZE_illegal_break_in_assign_var ->
      "illegal break when awaiting assignment"
  | ZE_illegal_break_in_start_choices ->
      "illegal break in start-choices"
  | ZE_illegal_break_in_handler ->
      "illegal break in handler"
  | ZE_illegal_finish_choice ->
      "illegal finish-choice"
  | ZE_illegal_finish_choice_in_assign_var ->
      "illegal finish-choice when awaiting assignment"
  | ZE_illegal_finish_choice_in_handler ->
      "illegal finish-choice in handler"
  | ZE_illegal_finish_choice_in_loop ->
      "illegal finish-choice in loop"
  | ZE_illegal_continue_choice ->
      "illegal continue-choice"
  | ZE_illegal_continue_choice_in_assign_var ->
      "illegal continue-choice when awaiting assignment"
  | ZE_illegal_continue_choice_in_loop ->
      "illegal continue-choice in loop"
  | ZE_illegal_continue_choice_in_handler ->
      "illegal continue-choice in handler"
  | ZE_illegal_continue_choice_in_failing_handler ->
      "illegal continue-choice in failing handler"
  | ZE_illegal_fail_choice ->
      "illegal fail-choice"
  | ZE_illegal_fail_choice_in_assign_var ->
      "illegal fail-choice when awaiting assignment"
  | ZE_illegal_fail_choice_in_loop ->
      "illegal fail-choice in loop"
  | ZE_illegal_fail_choice_in_handler ->
      "illegal fail-choice in handler"
  | ZE_illegal_fail_choice_in_success_handler ->
      "illegal fail-choice in success handler"
  | ZE_illegal_fail_in_assign_var ->
      "illegal fail when awaiting assignment"
  | ZE_illegal_fail_in_start_choice ->
      "illegal fail-choice in start-choice"
  | ZE_illegal_fail_in_handler ->
      "illegal fail in handler"

let error_msg e =
  Printf.sprintf "Internal Error: %s" (exn_msg e)

type next =
  | N_in_block   of bivalent_instr * zscf
  | N_in_handler of linear_instr   * zscf
  | N_done_success
  | N_done_failure

let rec next (l: Location.t) z : next =
  let rec search z =
    match z with
      | Zscf_root _ ->
          N_done_success
      | Zscf_assign_var _ ->
          (* This continuation is expecting a value and cannot be
             stepped over. *)
          let err = ZE_illegal_next_in_assign_var in
          raise (Error (l, err))
      | Zscf_block ((p, h :: t), z') ->
          let z = Zscf_block ((h :: p, t), z') in
          N_in_block (h, z)
      | Zscf_block ((_, []), z) ->
          search z
      | Zscf_do ((p, h :: t), eh, z') ->
          let z = Zscf_do ((h :: p, t), eh, z') in
          N_in_block (h, z)
      | Zscf_do ((_, []), _, z) ->
          search z
      | Zscf_doh (sb, h, (p, i :: t), z') ->
          let z = Zscf_doh (sb, h, (i :: p, t), z') in
          N_in_handler (i, z)
      | Zscf_doh (_, H_success, (_, []), z) ->
          (* Resume at the next instruction. *)
          search z
      | Zscf_doh (_, H_failure, (_, []), z) ->
          (* Resume in an enclosing handler. *)
          fail l z
      | Zscf_loop (f, (p, h :: t), z') ->
          let z = Zscf_loop (f, (h :: p, t), z') in
          N_in_block (h, z)
      | Zscf_loop (_, ([], []), z) ->
          (* This should not have been validated, but operationally it
             is treated as a nop. *)
          search z
      | Zscf_loop (f, (rb, []), z') ->
          (* Go back to the first instruction in the block. *)
          let h, bz = match List.rev rb with
              | []     -> assert false (* The earlier case handles this.*)
              | h :: t -> h, ([h], t) in
          let z = Zscf_loop (f, bz, z') in
          N_in_block (h, z)
      | Zscf_ift (av, (p, h :: t), eb, z') ->
          let z = Zscf_ift (av, (h :: p, t), eb, z') in
          N_in_block (h, z)
      | Zscf_ift (_, (_, []), _, z) ->
          search z
      | Zscf_ife (av, tb, (p, h :: t), z') ->
          let z = Zscf_ife (av, tb, (h :: p, t), z') in
          N_in_block (h, z)
      | Zscf_ife (_, _, (_, []), z) ->
          search z
      | Zscf_start_choices (f, muts, (p, h :: t), z) ->
          let z = Zscf_start_choices(f, muts, (h :: p, t), z) in
          N_in_block (h, z)
      | Zscf_start_choices (_, _, (_, []), z) ->
          search z in
  search z

and fail (l: Location.t) z : next =
  let rec search z =
    match z with
      | Zscf_root _ ->
          N_done_failure
      | Zscf_assign_var _ ->
          (* This continuation is expecting a value and cannot be
             failed. *)
          let err = ZE_illegal_fail_in_assign_var in
          raise (Error (l, err))
      | Zscf_block (_, z)
      | Zscf_loop (_, _, z)
      | Zscf_ift (_, _, _, z)
      | Zscf_ife (_, _, _, z) ->
          search z
      | Zscf_do (bz, (h, sh), z') ->
          (* Failures are handled in `do` blocks. *)
          let sb = zip_block bz in
          let eh = unseal_handler sh in
          let z  = Zscf_doh (sb, h, ([], eh), z') in
          next l z
      | Zscf_doh _ ->
          let err = ZE_illegal_fail_in_handler in
          raise (Error (l, err))
      | Zscf_start_choices _ ->
          (* We should be transitioning inside `start_choices` via the
             choice instructions. *)
          let err = ZE_illegal_fail_in_start_choice in
          raise (Error (l, err)) in
  search z

(* Specialized helpers for control flow. *)

let break (l: Location.t) (z: zscf) : zscf =
  let rec search z =
    match z with
      | Zscf_root _ ->
          let err = ZE_no_loop_for_break in
          raise (Error (l, err))
      | Zscf_loop (_, _, z) ->
          z
      | Zscf_assign_var _ ->
          (* The continuation is expecting a value. *)
          let err = ZE_illegal_break_in_assign_var in
          raise (Error (l, err))
      | Zscf_block (_, z)
      | Zscf_do (_, _, z)
      | Zscf_ift (_, _, _, z)
      | Zscf_ife (_, _, _, z) ->
          search z
      | Zscf_doh _ ->
          let err = ZE_illegal_break_in_handler in
          raise (Error (l, err))
      | Zscf_start_choices _ ->
          let err = ZE_illegal_break_in_start_choices in
          raise (Error (l, err)) in
  search z

let finish_choice (l: Location.t) (z: zscf) : zscf =
  let rec search z =
    match z with
      | Zscf_root _ ->
          let err = ZE_illegal_finish_choice in
          raise (Error (l, err))
      | Zscf_start_choices (_, _, _, z) ->
          z
      | Zscf_assign_var (_, _) ->
          let err = ZE_illegal_finish_choice_in_assign_var in
          raise (Error (l, err))
      | Zscf_block (_, z)
      | Zscf_do (_, _, z)
      | Zscf_ift (_, _, _, z)
      | Zscf_ife (_, _, _, z) ->
          search z
      | Zscf_loop _ ->
          let err = ZE_illegal_finish_choice_in_loop in
          raise (Error (l, err))
      | Zscf_doh _ ->
          let err = ZE_illegal_finish_choice_in_handler in
          raise (Error (l, err)) in
  search z

let continue_choice (l: Location.t) (z: zscf) : zscf =
  let rec search z =
    match z with
      | Zscf_root _ ->
          let err = ZE_illegal_continue_choice in
          raise (Error (l, err))
      | Zscf_start_choices (_, _, (_, _ :: _), _) ->
          z (* this is pointing at the next choice *)
      | Zscf_start_choices (_, _, (_, []), _) ->
          let err = ZE_illegal_continue_choice in
          raise (Error (l, err))
      | Zscf_assign_var (_, _) ->
          let err = ZE_illegal_continue_choice_in_assign_var in
          raise (Error (l, err))
      | Zscf_block (_, z)
      | Zscf_do (_, _, z)
      | Zscf_ift (_, _, _, z)
      | Zscf_ife (_, _, _, z) ->
          search z
      | Zscf_loop _ ->
          let err = ZE_illegal_continue_choice_in_loop in
          raise (Error (l, err))
      (* continue-choice should be the last instruction in a handler. *)
      | Zscf_doh (_, _, (_, _::_), _) ->
          let err = ZE_illegal_continue_choice_in_handler in
          raise (Error (l, err))
      (* continue-choice can only occur in a success handler. *)
      | Zscf_doh (_, H_failure, (_, []), _) ->
          let err = ZE_illegal_continue_choice_in_failing_handler in
          raise (Error (l, err))
      | Zscf_doh (_, H_success, (_, []), z) ->
          z in
  search z

let fail_choice (l: Location.t) (z: zscf) : next =
  let rec search z =
    match z with
      | Zscf_root _ ->
          let err = ZE_illegal_fail_choice in
          raise (Error (l, err))
      | Zscf_assign_var _ ->
          let err = ZE_illegal_fail_choice_in_assign_var in
          raise (Error (l, err))
      | Zscf_start_choices (_, _, _, z) ->
          (* Escape to the closest handler. *)
          fail l z
      | Zscf_block (_, z)
      | Zscf_do (_, _, z)
      | Zscf_ift (_, _, _, z)
      | Zscf_ife (_, _, _, z) ->
          search z
      | Zscf_loop _ ->
          let err = ZE_illegal_fail_choice_in_loop in
          raise (Error (l, err))
      (* fail-choice should be the last instruction in a handler. *)
      | Zscf_doh (_, _, (_, _::_), _) ->
          let err = ZE_illegal_fail_choice_in_handler in
          raise (Error (l, err))
      (* fail-choice can only occur in a failing handler. *)
      | Zscf_doh (_, H_success, (_, []), _) ->
          let err = ZE_illegal_fail_choice_in_success_handler in
          raise (Error (l, err))
      | Zscf_doh (_, H_failure, (_, []), z) ->
          search z in
  search z
