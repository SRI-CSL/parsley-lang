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

(* This IR lowers control-flow to block-structured primitives.
   Retaining block-structure instead of going directly to a CFG helps
   clarify issues around stack frame design and the implementation of
   backtracking, as well as making it easier to support a backend with
   block-structured control-flow such as WASM.

   WASM generation is harder from a CFG since inefficient code may be
   generated when attempts are made to reconstruct structured
   control-flow after it has been flattened in a CFG.  It is unlikely
   that the current Parsley CFG is irreducible, but it is best to be
   future-proof.  More details on the problem:
   http://troubles.md/why-do-we-need-the-relooper-algorithm-again/
   https://medium.com/leaningtech/solving-the-structured-control-flow-problem-once-and-for-all-5123117b1ee2
   *)

open Parsing
open Typing
open Anf
open Dfa

(* unique identifier for instructions. *)

type instr_id = int
type instr_id_gen = unit -> instr_id

let mk_id_gen () : instr_id_gen =
  let id = ref 0 in
  fun () -> let i = !id in
            incr id;
            i

(* bit-matching primitives *)

(* A bound on the expected number of matched bits. *)
type matched_bits_bound =
  | MB_exact of int (* the bound is exact *)
  | MB_below of int (* the matched number has to be <= the bound *)

(* The above bound as well as a specified bit-pattern, to be matched
   for padding. *)
type matched_bits_predicate =
  matched_bits_bound * Ast.bv_literal

(* The nodes in the IR for the grammar language roughly correspond to
   instructions.  These instructions are split into linear
   instructions, atomic bivalent instructions and block-structured
   control (or control block) instructions.  Linear instructions can
   only succeed, or fail the whole parse.  Atomic bivalent
   instructions could succeed or fail, with the failure continuation
   specified by the enclosing control block instruction.  Control
   block are bivalent instructions that contain other instructions.

   A slightly more accurate definition: a 'linear' instruction cannot
   trigger control flow (or 'escape') to a failure handler.  Or, if it
   fails, the whole parse execution itself fails entirely; no
   backtracking is performed.
 *)

(* We track mutations to variables within each frame context, so that
   those variables can be saved and restored for backtracking.
   Variables are tagged to identify which frame they were allocated
   in.  A mutation can only be performed on a variable that was
   allocated in a frame (or scope) that is visible to the context in
   which the mutation is performed.
 *)
module FrameMap = Map.Make(struct type t = frame_id
                                  let compare = compare
                           end)


(* Handler type. *)
type handle =
  | H_success
  | H_failure

type linear_desc =
  (* expression evaluation *)

  (* Evaluate the expression and assign it to a variable. *)
  | L_assign of var * aexp

  (* Create an entry for an internal function and assign it to a
     variable.  Since there are no first-class functions, this is
     usually done during initialization.  The VSet contains all the
     temporary variables created in lowering the body. *)
  | L_assign_fun of var * var list * aexp * VSet.t

  (* Module exports of values and functions *)
  | L_assign_mod_var of Ast.modident * Ast.ident * aexp
  | L_assign_mod_fun of Ast.modident * Ast.ident * var list * aexp * VSet.t

  (* side-effects *)

  (* Any return value from the action will be handled by an `assign`. *)
  | L_action of astmt list

  (* The mechanism for the matching and extraction of matched bits is
     the following:

     . A bit-sensitive parsing mode is explicitly entered using
       `enter_bitmode` before any bit-wise parsing operation.  This
       must be at a byte-aligned offset; this offset is restored on
       any bit-wise parsing failure.

     . The current bit-cursor location is marked (`mark_bit_cursor`).

     . The cursor is updated according to the bit-matching construct
       (bitvector, align, pad, bitfield).

     . The bits from the marked position to the current cursor are
       collected into a variable holding the match
       (`collect_bits`). An expected number of bits (or bound on this
       number) is specified as a check on correctness.

     . When a sequence of bit-wise parsing operations are finished,
       the normal parsing mode is restored using `exit_bitmode` at a
       byte-aligned offset.

     . When a bit-wise parsing operation fails (at any bit offset),
       the normal parsing mode is restored using `fail_bitmode` to the
       byte-aligned view offset at which the sequence of bit-wise
       parsing operations began with `enter_bitmode`.

       It is an internal error if there is no marked position at the
       time of `collect_bits`.

       If the matched bits are not being bound by a variable, the
       `mark_bit_cursor` and `collect_bits` are omitted. *)

  (* Enter/exit the bitwise parsing mode *)
  | L_enter_bitmode
  | L_exit_bitmode
  | L_fail_bitmode  (* This exits the bitwise mode, but doesn't really
                     * fail.  The idea is this should only be used in
                     * a failure handler; but otherwise it is like
                     * `exit_bitmode`.  Perhaps we can just use
                     * `exit_bitmode`?
                     *)

  (* Mark bit-cursor location *)
  | L_mark_bit_cursor

  (* Collect matched bits from the marked position into a variable,
     and optionally interpret as a bitfield. *)
  | L_collect_bits of
      var * matched_bits_bound * TypingEnvironment.bitfield_info option

  (* view control *)

  (* The view state is organized into a current-view register and a
     view stack.  Starting a view excursion causes the current view to
     be pushed onto the stack, and the excursion view to become the
     current view.  Returning from the excursion causes the top-most
     element from the view stack to be popped and become the current
     view.

     There is an asymmetry in these two instructions: `push-view`
     leaves the current-view register intact, but pushes its value
     onto the view-stack.  `pop-view` pops the top-most value from the
     stack and puts it into the current-view register, thus modifying
     both the stack and the register.  This asymmetry is a consequence
     of the design choice discussed below.

     `drop-view` drops the top-most entry on the stack. *)

  | L_push_view
  | L_pop_view
  | L_drop_view

  (* The two view setters below are equivalent in that each could be
     expressed in terms of the other, via some glue ANF.  However,
     that would require a hidden View API to modify the view,
     e.g. `View.set_cursor()` or `View.set_view()`.  This API would
     need to be hidden, and would violate the separation of concerns:
     the expression language should not be able to directly
     (i.e. without going through the grammar language) modify the
     cursor or view location.

     To avoid this kind of hidden violation of the separation of
     concerns, each of the two is a primitive in the CFG IR.  Each
     modifies the current-view register: `set_view` puts its argument
     into the register, `set_pos` adjusts the cursor of the view in
     the register. *)

  | L_set_view of var
  | L_set_pos of var

  (* Choice frame manipulation for backtracking: these should be the
     last instructions in the block they appear in.  *)

  (* Inner backtrack: restore the view and variables from the innermost
     choice frame, and continue to the next instruction. *)
  | L_continue_choice

  (* Discard the innermost choice frame, and continue to the
     instruction after the `start_choice`. *)
  | L_finish_choice

  (* Backtrack: restore the view and variables from the innermost
     choice frame, discard the frame, and continue with the now
     innermost failure handler. *)
  | L_fail_choice

type linear_instr =
  {li:     linear_desc;
   li_typ: TypedAst.typ;
   li_loc: Location.t;
   li_id:  instr_id}

(* The basic bivalent instruction type, which includes linear and
   structured control instructions. *)
type bivalent_desc =
  (* Linear instructions are trivially bivalent. *)
  | B_linear of linear_instr

  (* Structured control blocks. *)
  | B_control of ctrl_instr

  (* Unconditional control flow: *)
  (* Fail to the nearest failure handler *)
  | B_fail
  (* Break out of loop.  This should be the last instruction in the
     block it appears in. *)
  | B_break  (* invariant: can only appear inside a loop block. *)

  (* Different kinds of matching instructions. *)

  (* Bit-mode matching: *)
  (* Match a specified number of bits. *)
  | B_bits of int
  (* Align to the specified width. *)
  | B_align of int
  (* Match the specified number of bits as padding.  The padding
     pattern is specified in the following `collect_bits`. *)
  | B_pad of int

  (* Collect matched bits from the marked position and check the
     specified predicate.  If it succeeds, `collect_checked_bits`
     assigns the collected bitvector to the specified variable.
     `check_bits` does the same except that it does not assign
     the matched bits to any variable. *)
  | B_collect_checked_bits of var * matched_bits_predicate
  | B_check_bits of matched_bits_predicate

  (* Constraint: the var should have been bound to the value
     of the constraint expression. *)
  | B_constraint of var

  (* Call the DFA for a regular expression.  On a successful match,
     assign the specified variable to the match. *)
  | B_exec_dfa of Automaton.dfa * var

  (* Special case for tag scanning. *)
  | B_scan of (Ast.literal * Ast.scan_direction) * (*return*) var

  (* Call the CFG for the specified non-terminal with the specified
     expressions for the inherited attributes. *)
  | B_call_nonterm of
      Anf.modul * Ast.ident * (Ast.ident * var) list * (*return*) var

  (* Suspension constraint (or dynamic assertion): Suspend the
     parsing machine until the constraint is satisfied.  This
     requires that the instruction is the first one to be executed on
     resuming the parse after a suspension. *)
  | B_require_remaining of var (* view *) * var (* nbytes *)

and bivalent_instr =
  {bi:     bivalent_desc;
   bi_loc: Location.t;
   bi_id:  instr_id}

and block = bivalent_instr list

and handler = linear_instr list

(* Since blocks under construction are in reverse order, they need to
   be `sealed` (i.e. reversed) before being embedded in other
   structures like control instructions. *)
and sealed_block   = [`Sealed of block]
and sealed_handler = [`Sealed of handler]

(* A control block exit handler can only have linear instructions so
   that it cannot fail. *)
and exit_handler = handle * sealed_handler

(* Structured control block instructions. *)
and ctrl_desc =
  (* If all the bivalent instructions in the 'do' block execute
     successfully, the 'do' instruction executes successfully (and the
     instructions in the handler do not execute).  If any instruction
     in the block fails, the subsequent instructions in the block do
     not execute, and control flows to the linear instructions in the
     handler and execute to the end of the handler.  If the handler is
     marked Succ, the 'do' instruction itself succeeds, otherwise it
     fails.  Note that instructions in the handler cannot fail by
     construction. *)
  | C_do of sealed_block * exit_handler

  (* A `loop` block is exited via `break` or a match failure.  The
     flag indicates whether the loop is potentially infinite and hence
     can only be exited by match failure (true) or whether it expects
     to terminate and hence can be broken out by `break`. *)
  | C_loop of bool * sealed_block

  (* Conditional control block. *)
  | C_if of var * sealed_block * sealed_block

  (* Choice combinator block.  Creates a choice frame, initialized
     with current view and the specified variables that will need
     restoration when backtracking. *)
  | C_start_choices of frame_id * mutations FrameMap.t * sealed_block

and ctrl_instr =
  {ci:      ctrl_desc;
   ci_loc:  Location.t;
   ci_id:   instr_id}

module StringMap = Map.Make(String)

(* The entry describing a non-terminal in the IR.  The instructions
   for the non-terminal are stored separately, since this entry is
   needed for each non-terminal before their IR instructions can be
   generated. *)

type nt_entry =
  {nt_name:      Ast.ident;
   (* each inherited attribute and the corresponding var used for it
      in the CFG *)
   nt_inh_attrs: (var * TypedAst.typ) StringMap.t;
   (* type of the return value after parsing this non-terminal *)
   nt_typ:       TypedAst.typ;
   (* the generated code for the non-terminal *)
   nt_code:      sealed_block;
   (* a successfully matched value will be bound to this variable *)
   nt_retvar:    var;
   (* the location this non-term was defined *)
   nt_loc:       Location.t}

module ValueMap = Map.Make(struct type t = modul * string
                                  let compare = compare
                           end)

(* The IR for the entire specification. *)
type spec_scf =
  {scf_globals:       nt_entry ValueMap.t; (* indexed by non-terminal name *)
   scf_statics:       sealed_block; (* constants and functions *)
   scf_foreigns:      TypedAst.ffi_decl ValueMap.t;
   (* Debugging state for the interpreter. *)
   scf_tenv:          TypingEnvironment.environment;
   scf_venv:          VEnv.t}

(* Instruction utilities. *)

let mk_linst d t l i : linear_instr =
  {li     = d;
   li_typ = t;
   li_loc = l;
   li_id  = i}

let mk_binst d l i : bivalent_instr =
  {bi     = d;
   bi_loc = l;
   bi_id  = i}

let mk_cinst c l i : ctrl_instr =
  {ci     = c;
   ci_loc = l;
   ci_id  = i}

let mk_l2b d t l i : bivalent_instr =
  let li = mk_linst d t l i in
  mk_binst (B_linear li) l i

let mk_c2b c l i : bivalent_instr =
  let ci = mk_cinst c l i in
  mk_binst (B_control ci) l i

let can_fail_implicitly (i: bivalent_instr) : bool =
  match i.bi with
    | B_linear _ | B_control _ | B_fail | B_break
    | B_require_remaining _
      -> false
    | B_bits _ | B_align _ | B_pad _
    | B_collect_checked_bits _ | B_check_bits _
    | B_constraint _ | B_exec_dfa _ | B_scan _
    | B_call_nonterm _
      -> true

(* Block and handler utilities. *)

let init_block = []

let add_instr i b =
  i :: b

(* Instructions are added to blocks by consing, and hence are in
   reverse order.  The sealing operation corrects this.  Unsealing
   returns the instructions in execution order. *)
let seal_block (b: block) : sealed_block =
  `Sealed (List.rev b)

let seal_handler (h: handler) : sealed_handler =
  `Sealed (List.rev h)

let unseal_block (b: sealed_block) : block =
  match b with
    | `Sealed b -> b

let unseal_handler (h: sealed_handler) : handler =
  match h with
    | `Sealed h -> h

let seq_blocks (prolog: block) (epilog: block) : block =
(* unsealed `e` and `p` are in reverse order, so `p` needs to end up
   at the end of the list. *)
  List.rev_append (List.rev epilog) prolog

(* Errors *)

type error =
  | Unbound_return_expr
  | Unsupported_construct of string
  | Nonterm_variable_required of Ast.ident

exception Error of Location.t * error

let error_msg = function
  | Unbound_return_expr ->
      "The return expression in this action block is not used."
  | Unsupported_construct s ->
      Printf.sprintf "CFG generation for `%s' is currently unsupported." s
  | Nonterm_variable_required ntd ->
      Printf.sprintf "Non-terminal `%s' requires a variable to indicate the matched value."
        (Location.value ntd)

(* The context for code generation. *)

(* The code generation context tracks the frames in scope in a stack. *)
type context =
  {(* The typing environment. *)
   ctx_tenv:      TypingEnvironment.environment;
   (* The generated code for non-terminals processed so far. *)
   ctx_toc:       nt_entry ValueMap.t;
   (* The current variable environment. *)
   ctx_venv:      VEnv.t;
   (* Intermediate re forms for regexp non-terminals, to be used for
      inlining when generating DFAs. *)
   ctx_re_env:    Automaton.re_env;
   (* Whether the current mode is bit-wise. *)
   ctx_bitmode:   bool;
   (* Current frame id *)
   ctx_frame:     frame_id;
   (* Stack frames in scope, with the current (i.e. innermost) frame
      at the top (head) of the stack (list). *)
   ctx_stack:     frame_id list;
   (* Frame id generator *)
   ctx_frame_gen: frame_gen;
   (* Mutations *)
   ctx_mutations: mutations FrameMap.t;
   (* Instruction id allocator *)
   ctx_id_gen:    instr_id_gen}

let add_frame (ctx: context) (f: frame_id) : context =
  {ctx with ctx_frame = f;
            ctx_stack = f :: ctx.ctx_stack}

let pop_frame (ctx: context) : context =
  match ctx.ctx_stack with
    | _ :: ((f :: _) as stk) -> {ctx with ctx_frame = f;
                                          ctx_stack = stk}
    | _                      -> assert false

(* Context conversions *)

(* The statement context is a projection of the top-level context. *)
let to_stm_ctx (ctx: context) : anf_stm_ctx =
  {anfs_tenv      = ctx.ctx_tenv;
   anfs_venv      = ctx.ctx_venv;
   anfs_frame     = ctx.ctx_frame;
   anfs_stack     = ctx.ctx_stack;
   anfs_frame_gen = ctx.ctx_frame_gen;
   anfs_muts      = VMap.empty}

let to_exp_ctx (ctx: context) : anf_exp_ctx =
  mk_exp_ctx (to_stm_ctx ctx)

let of_stm_ctx (ctx: context) (sc: anf_stm_ctx) : context =
  let mutations =
    match FrameMap.find_opt sc.anfs_frame ctx.ctx_mutations with
      | None ->
          FrameMap.add sc.anfs_frame sc.anfs_muts ctx.ctx_mutations
      | Some m ->
          let m = union_mutations m sc.anfs_muts in
          FrameMap.add sc.anfs_frame m ctx.ctx_mutations in
  {ctx with ctx_venv      = sc.anfs_venv;
            ctx_mutations = mutations}

(* This is inefficient but corresponds more closely with a formal
   specification. *)
let of_exp_ctx (ctx: context) (ec: anf_exp_ctx) : context =
  of_stm_ctx ctx (fold_exp_ctx (to_stm_ctx ctx) ec)
