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

open Parsing
open Typing
open Flow
open Anf
open Dfa

(* source-level regexps, rule-elements, rules and non-terminals *)
type regexp         = (typ, TypeInfer.varid) Ast.regexp
type rule_elem      = (typ, TypeInfer.varid) Ast.rule_elem
type rule           = (typ, TypeInfer.varid) Ast.rule
type non_term_defn  = (typ, TypeInfer.varid) Ast.non_term_defn
type format_decl    = (typ, TypeInfer.varid) Ast.format_decl

(* source-level spec *)
type format         = (typ, TypeInfer.varid) Ast.format
type program        = (typ, TypeInfer.varid) Ast.program

(* The IR for the grammar language is a control-flow graph (CFG) with
   explicit control flow for the grammar matching.  The most important
   aspect that is made explicit is the handling of match failure and
   the next choice to back-track to.

   Each non-terminal definition is represented by its own CFG.  Any
   embedded expressions are represented by their ANF forms.  The CFG
   and ANF share the variable representation.  *)

(* A bound on the expected number of matched bits. *)
type matched_bits_bound =
  | MB_exact of int (* the bound is exact *)
  | MB_below of int (* the matched number has to be <= the bound *)

(* The above bound as well as a specified bit-pattern, to be matched
   for padding. *)
type matched_bits_predicate =
  matched_bits_bound * Ast.bv_literal

(* An optional variable to which the matched return value needs to be
   bound.  The boolean indicates whether this is a fresh variable
   (true) that needs to be initialized, or an existing variable
   (false) that needs to be assigned.

   Due to the presence of loops, a variable marked fresh may already
   exist since it may occur in a loop body.  The invariant that should
   hold, however, is that a non-fresh variable should already exist in
   the dynamic environment.  *)
type return = (var * bool) option

(* The various types of internal nodes of a block in the CFG.  These
   are the open-open nodes with linear control flow, and are
   typically directly related to elements of the grammar language. *)

type gnode_desc =
  (* expression evaluation *)

  (* Evaluate the expression and assign it to a possibly fresh
     variable *)
  | N_assign of var * bool * aexp

  (* Create an entry for a function and assign it to a fresh
     variable.  Since there are no first-class functions, this is
     usually done during initialization. *)
  | N_assign_fun of var * var list * aexp

  (* side-effects *)

  (* Any return value from the action will be handled by an _assign *)
  | N_action of astmt list

  (* The mechanism for the matching and extraction of matched bits is
     the following:

     . the current bit-cursor location is marked (N_mark_bit_cursor)

     . the cursor is updated according to the bit-matching construct
       (bitvector, align, pad, bitfield)

     . the bits from the marked position to the current cursor are
       collected into a variable holding the match (N_collect_bits).
       An expected number of bits (or bound on this number) is
       specified as a check on correctness.

     It is an internal error if there is no marked position at the
     time of N_collect_bits.

     If the matched bits are not being bound by a variable, the
     N_mark_bit_cursor and N_collect_bits are omitted.
   *)

  (* Match a specified number of bits *)
  | N_bits of int
  (* Align to the specified width *)
  | N_align of int
  (* Match the specified number of bits as padding.  The padding
     pattern is specified in the following N_collect_bits node *)
  | N_pad of int
  (* Mark bit-cursor location *)
  | N_mark_bit_cursor
  (* Collect matched bits from the marked position into a variable,
     which may be fresh. *)
  | N_collect_bits of var * bool * matched_bits_bound

  (* view control *)

  (* The view state is organized into a current-view register and a
     view stack.  Starting a view excursion causes the current view to
     be pushed onto the stack, and the excursion view to become the
     current view.  Returning from the excursion causes the top-most
     element from the view stack to be popped and become the current
     view.

     There is an asymmetry in these two instructions: push-view leaves
     the current-view register intact, but pushes its value onto the
     view-stack.  pop-view pops the top-most value from the stack and
     puts it into the current-view register, thus modifying both the
     stack and the register.  This asymmetry is a consequence of the
     design choice discussed below.

     View values on the stack are not modified due to excursions, even
     with views derived from these values.  TODO: confirm this.  *)

  | N_push_view
  | N_pop_view

  (* The two view setters below are equivalent in that each could be
     expressed in terms of the other, via some glue ANF.  However,
     that would require a hidden View API to modify the view,
     e.g. View.set_cursor() or View.set_view().  This API would need
     to be hidden, and would violate the separation of concerns: the
     expression language should not be able to directly (i.e. without
     going through the grammar language) modify the cursor or view
     location.

     To avoid this kind of hidden violation of the separation of
     concerns, each of the two is a primitive in the CFG IR.  Each
     modifies the current-view register: set-view puts its argument
     into the register, set-pos adjusts the cursor of the view in the
     register. *)

  | N_set_view of var
  | N_set_pos of var

type gnode =
  {node: gnode_desc;
   node_typ: typ;
   node_loc: Location.t}

let mk_gnode n t l =
  {node = n;
   node_typ = t;
   node_loc = l}

(* Labels are used to designate the unique entry node of a block, and
   therefore also used to designate the block itself.  The interior of
   a block contains CFG nodes that have linear control flow, and the
   block is terminated by a node to transfer control to another block
   by specifying the label of the target block.

   Labels are of two types: static and dynamic.  Static labels are
   used to designate fixed control-flow targets, i.e. targets that do
   not change during execution.  Dynamic labels are used when a target
   is only known during execution.

   When lowering the rules for a non-terminal to a CFG, the success
   and continuation targets for the non-terminal are only known during
   execution, and may change for each invocation.  Hence, the CFG for
   a non-terminal is generated using dynamic labels for the success
   and failure continuations, and these labels will be use to transfer
   control to the targets in effect at the time the CFG for the
   non-terminal is executed.

   The entry node of a block is always static; however, jump targets,
   failure continuations and success continuations may be dynamic.
 *)

type label =
  | L_static of Label.label
  | L_dynamic of Label.label

let fresh_static () =
  L_static (Label.fresh_label ())

let fresh_dynamic () =
  L_dynamic (Label.fresh_label ())

let is_static = function
  | L_static _  -> true
  | L_dynamic _ -> false

let is_dynamic = function
  | L_static _  -> false
  | L_dynamic _ -> true

let raw_label_of = function
  | L_static l  -> l
  | L_dynamic l -> l

let label_to_string l =
  match l with
    | L_static  l -> Printf.sprintf "S%s" (Label.to_string l)
    | L_dynamic l -> Printf.sprintf "D%s" (Label.to_string l)

(* Handling match failures, or back-tracking:

   This is done with a stack of labels, or failconts, that point to
   blocks from which execution should be resumed.  On a failure, the
   top-most failcont label from the stack is popped, and execution
   resumed from the block pointed to by the label.

   All modifications to variable state are stratified according to the
   failcont context in which they are performed.  On a match failure,
   all state updates since the last push_failcont are undone, and that
   execution resumes from that failcont.  On a pop_failcont, the state
   updates since the last push_failcont are promoted to the stratum of
   the next lower failcont.  This is because valid pop_failconts are
   always done on success paths, where variable state should not be
   rolled back.

   This can be used to perform a limited amount of garbage collection:
   on error, all variables allocated since the last push_failcont can
   be deallocated when the failcont stack is popped.

 *)

(* The node structure of the CFG *)

module Node = struct
  (* Other nodes mostly concerned with control flow and book-keeping *)
  type ('e, 'x, 'v) node =
    (* block entry, denoted by an implicitly static label *)

    | N_label: Location.t * Label.label -> (Block.c, Block.o, unit) node

    (* non-control-flow blocks *)

    | N_gnode: gnode -> (Block.o, Block.o, unit) node

    (* push or pop a failure continuation on the failcont stack *)
    | N_push_failcont: Location.t * label -> (Block.o, Block.o, unit) node
    | N_pop_failcont:  Location.t * label -> (Block.o, Block.o, unit) node

    (* block exits *)

    (* Collect matched bits from the marked position and check the
       specified predicate.  If it succeeds, N_collect_checked_bits
       assigns the collected bitvector to the specified variable,
       which may be fresh, and jumps to the first label; otherwise, it
       fails to the second label.  N_check_bits does the same except
       that it does not assign the matched bits to any variable. *)
    | N_collect_checked_bits:
        Location.t * var * bool * matched_bits_predicate
        * label * label
        -> (Block.o, Block.c, unit) node
    | N_check_bits:
        Location.t * matched_bits_predicate
        * label * label
        -> (Block.o, Block.c, unit) node

    (* forward jumps *)
    | N_jump: Location.t * label -> (Block.o, Block.c, unit) node

    (* Constrained jump: the var should have been bound to the value
       of the constraint expression, and the label is the success
       continuation.  If the constraint fails (evaluates to false),
       rewind to the top-most failcont on the failcont stack, which is
       specified as the second label (to enable a dynamic check for
       code-generation errors, and a more accurate successors
       function). *)
    | N_constraint: Location.t * var * label * label
                    -> (Block.o, Block.c, unit) node

    (* Conditional branch: similar to above, except that the label for
       the failed condition is explicitly specified.  A failed
       condition does not have failcont semantics; i.e. jumping to the
       label for the failed case counts as forward progress. *)
    | N_cond_branch: Location.t * var * label * label
                     -> (Block.o, Block.c, unit) node

    (* Call the DFA for a regular expression.  On a successful match,
       assign the specified variable to the match, and continue at the
       first specified label.  A failure rewinds to the top-most
       failcont on the failcont stack, which is specified as the
       second label (see N_constraint above). *)
    | N_exec_dfa: dfa * var * label * label
                  -> (Block.o, Block.c, unit) node

    (* Call the CFG for the specified non-terminal with the specified
       expressions for the inherited attributes.  On a successful
       continuation, continue at the first specified label.  The
       second label is the current failcont.
       At runtime: the specified labels are the dynamic success
       and failure continuations, which get mapped to the static
       succcont and failcont for the non-terminal's CFG, as specified
       in its nt_entry.
     *)
    | N_call_nonterm:
        Ast.ident * (Ast.ident * var) list * return * label * label
        -> (Block.o, Block.c, unit) node

  type entry_node  = (Block.c, Block.o, unit) node
  type linear_node = (Block.o, Block.o, unit) node
  type exit_node   = (Block.o, Block.c, unit) node

  let entry_label (type x v) (n: (Block.c, x, v) node) =
    match n with
      | N_label (_, l) -> l
      (* this should not be needed *)
      | _ -> assert false

  let successors (type e v) (n: (e, Block.c, v) node) =
    match n with
      | N_constraint (_, _, sc, fl)
      | N_cond_branch (_, _, sc, fl)
      | N_call_nonterm (_, _, _, sc, fl)
        -> [raw_label_of sc; raw_label_of fl]
      | N_jump (_, l) -> [raw_label_of l]
      (* this should not be needed *)
      | _ -> assert false
end

(* The CFG *)

module G = Graph.MkGraph (Node)
module B = G.Block

type opened = (Block.c, Block.o, unit) B.block
type closed = (Block.c, Block.c, unit) B.block

module StringMap = Map.Make(String)

(* The entry describing a non-terminal in the IR.  The CFG itself is
 * stored separately, since this entry is needed for each non-terminal
 * before their CFGs can be constructed. *)
type nt_entry =
  {nt_name: Ast.ident;
   (* each inherited attribute and the corresponding var used for it
    * in the CFG *)
   nt_inh_attrs: (var * typ) StringMap.t;
   (* type of the return value after parsing this non-terminal *)
   nt_typ: typ;
   (* the entry label for the CFG *)
   nt_entry: Label.label; (* is implicitly static *)
   (* a pair of success and failure continuations are assumed for the
      CFG.  these need to mapped to the current runtime success and
      failure continuations during execution *)
   nt_succcont: label;    (* should always be dynamic *)
   nt_failcont: label;    (* should always be dynamic *)
   (* a successfully matched value will be bound to this variable *)
   nt_retvar: var;
   (* the location this non-term was defined *)
   nt_loc: Location.t}

(* The 'grammar table-of-contents' maps each non-terminal name to its
   nt_entry.  It is only a ToC and not complete since it does not
   contain the actual CFGs. *)
module FormatGToC = Map.Make(struct type t = string
                                    let compare = compare
                             end)

(* This is the complete set of CFG blocks in the specification,
   indexed by their entry label. *)
module FormatIR = Map.Make(struct type t = Label.label
                                  let compare = compare
                           end)

(* the IR for the entire specification *)
type spec_ir =
  {ir_gtoc:          nt_entry FormatGToC.t;
   ir_blocks:        closed FormatIR.t;
   ir_statics:       opened; (* constants and functions *)
   ir_init_failcont: label;  (* should always be dynamic *)
   (* debugging state for the interpreter *)
   ir_tenv:          TypingEnvironment.environment;
   ir_venv:          VEnv.t}

(* The context for IR generation *)
type context =
  {(* the typing environment *)
   ctx_tenv: TypingEnvironment.environment;
   (* this will stay static during the construction of the IR *)
   ctx_gtoc: nt_entry FormatGToC.t;
   (* this will be updated during the construction with completed
      blocks *)
   ctx_ir:   closed FormatIR.t;
   (* the current variable environment *)
   ctx_venv: VEnv.t;
   (* the current failure continuation *)
   ctx_failcont: label; (* may be static or dynamic *)
   (* intermediate re forms for regexp non-terminals *)
   ctx_re_env:   re_env}

type error =
  | Unbound_return_expr of Location.t
  | Unsupported_construct of Location.t * string
  | Nonterm_variable_required of Ast.ident
exception Error of error

let msg = Location.msg

let error_msg = function
  | Unbound_return_expr l ->
      msg "%s:\n The return expression in this action block is not used."
        l
  | Unsupported_construct (l, s) ->
      msg "%s:\n IR generation for `%s' is currently unsupported."
        l s
  | Nonterm_variable_required ntd ->
      msg
        "%s:\n Non-terminal `%s' requires a variable to indicate the matched value."
        (Location.loc ntd) (Location.value ntd)
