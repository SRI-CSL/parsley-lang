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
type regexp         = (typ, TypeInfer.varid, Ast.mod_qual) Ast.regexp
type rule_elem      = (typ, TypeInfer.varid, Ast.mod_qual) Ast.rule_elem
type rule           = (typ, TypeInfer.varid, Ast.mod_qual) Ast.rule
type non_term_defn  = (typ, TypeInfer.varid, Ast.mod_qual) Ast.non_term_defn
type format_decl    = (typ, TypeInfer.varid, Ast.mod_qual) Ast.format_decl
type ffi_decl       = (typ, TypeInfer.varid, Ast.mod_qual) Ast.ffi_decl

(* source-level spec *)
type format         = (typ, TypeInfer.varid, Ast.mod_qual) Ast.format
type spec_module    = (typ, TypeInfer.varid) Ast.spec_module

(* The IR for the grammar language is a control-flow graph (CFG) with
   explicit control-flow for the grammar matching.  The most important
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
   bound. *)
type return = var option

(* There are two main types of internal nodes of a block in the CFG.
   The first (`gnode`) consists of the open-open nodes with linear
   control-flow, and are typically directly related to evaluation of
   the expression sublanguage, or adjusting the state of the parsing
   machine.  The second (`Node.node`) consist mainly of open-closed
   nodes with branching control-flow, and typically involve a parsing
   operation which could either succeed or fail. *)

type gnode_desc =
  (* expression evaluation *)

  (* Evaluate the expression and assign it to a variable. *)
  | N_assign of var * aexp

  (* Create an entry for an internal function and assign it to a
     variable.  Since there are no first-class functions, this is
     usually done during initialization.  The VSet contains all the
     temporary variables created in lowering the body. *)
  | N_assign_fun of var * var list * aexp * VSet.t

  (* Module exports of values and functions *)
  | N_assign_mod_var of Ast.modident * Ast.ident * aexp
  | N_assign_mod_fun of Ast.modident * Ast.ident * var list * aexp * VSet.t

  (* side-effects *)

  (* Any return value from the action will be handled by an `N_assign`. *)
  | N_action of astmt list

  (* The mechanism for the matching and extraction of matched bits is
     the following:

     . A bit-sensitive parsing mode is explicitly entered using
       `N_enter_bitmode` before any bit-wise parsing operation.  This
       must be at a byte-aligned offset; this offset is restored on
       any bit-wise parsing failure.

     . The current bit-cursor location is marked
       (`N_mark_bit_cursor`).

     . The cursor is updated according to the bit-matching construct
       (bitvector, align, pad, bitfield).

     . The bits from the marked position to the current cursor are
       collected into a variable holding the match
       (`N_collect_bits`). An expected number of bits (or bound on
       this number) is specified as a check on correctness.

     . When a sequence of bit-wise parsing operations are finished,
       the normal parsing mode is restored using `N_exit_bitmode`
       at a byte-aligned offset.

     . When a bit-wise parsing operation fails (at any bit offset),
       the normal parsing mode is restored using `N_fail_bitmode` to
       the byte-aligned view offset at which the sequence of bit-wise
       parsing operations began with N_enter_bitmode.

     It is an internal error if there is no marked position at the
     time of `N_collect_bits`.

     If the matched bits are not being bound by a variable, the
     `N_mark_bit_cursor` and `N_collect_bits` are omitted. *)

  (* Enter/exit the bitwise parsing mode *)
  | N_enter_bitmode
  | N_exit_bitmode
  | N_fail_bitmode

  (* Mark bit-cursor location *)
  | N_mark_bit_cursor

  (* Collect matched bits from the marked position into a variable,
     and optionally interpret as a bitfield. *)
  | N_collect_bits of
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

  | N_push_view
  | N_pop_view
  | N_drop_view

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
     modifies the current-view register: set-view puts its argument
     into the register, set-pos adjusts the cursor of the view in the
     register. *)

  | N_set_view of var
  | N_set_pos of var

type gnode =
  {node:     gnode_desc;
   node_typ: typ;
   node_loc: Location.t}

let mk_gnode n t l =
  {node     = n;
   node_typ = t;
   node_loc = l}

(* Labels are used to designate the unique entry node of a block, and
   therefore also used to designate the block itself.  The interior of
   a block contains CFG nodes that have linear control-flow, and the
   block is terminated by a node to transfer control to another block
   by specifying the label of the target block.

   Labels are of two types: static and virtual.  *Static* labels are
   used to designate control-flow targets within the CFG of a
   non-terminal.  A CFG always has two exits: a success or a failure
   continuation.  These are denoted by virtual labels.

   When a CFG of a non-terminal `A` calls into the CFG of another
   non-terminal `B` (via a `N_call_nonterm` node), the virtual exit
   labels of `B`'s CFG get mapped to the actual labels used for the
   continuations of the call (i.e. the labels in the `N_call_nonterm`
   node).  This mapping is done in the call-frame for the call in the
   control stack.

   The entry node of a block is always static.  *)

type raw_label = Label.label

type label =
  | L_static  of raw_label
  | L_virtual of raw_label

let fresh_static () =
  L_static (Label.fresh_label ())

let fresh_virtual () =
  L_virtual (Label.fresh_label ())

let is_static = function
  | L_static _  -> true
  | L_virtual _ -> false

let is_virtual = function
  | L_static _  -> false
  | L_virtual _ -> true

let raw_label_of = function
  | L_static  l -> l
  | L_virtual l -> l

let string_of_label l =
  match l with
    | L_static  l -> Printf.sprintf "S%s" (Label.to_string l)
    | L_virtual l -> Printf.sprintf "V%s" (Label.to_string l)

module LabelOrdSet = struct type t = raw_label
                            let compare = compare
                     end
module LabelSet = Set.Make(LabelOrdSet)

(* The node structure of the CFG *)

module Node = struct

  (* The `node` type mainly consists of nodes that perform actual
     parsing actions or evaluate constraints or conditions, and hence
     which can branch (and hence 'exit' the IR block) due to the
     action either succeeding or failing, and nodes that are purely
     for control-flow between blocks such as jumps, calls and returns.

     The type also includes as special cases the book-keeping entry
     node `N_label`, and the linear open-open `N_gnode gnode` nodes
     described above.

     The CFG for a single non-terminal consists of a connected set of
     blocks containing these nodes.  Control transfer between the CFGs
     of different non-terminals is effected by the `N_call_nonterm`
     and `N_return` nodes, which implement bracketed cross-CFG
     control-flow.  *)

  type ('e, 'x, 'v) node =
    (* block entry node, denoted by an implicitly static label, and
       containing back-pointers to its calling blocks *)
    | N_label: Location.t * Label.label * LabelSet.t -> (Block.c, Block.o, unit) node

    (* non-control-flow or 'linear' nodes *)
    | N_gnode: gnode -> (Block.o, Block.o, unit) node

    (* exit nodes *)

    (* bit-mode matching *)

    (* Match a specified number of bits *)
    | N_bits: Location.t * int * label * label
              -> (Block.o, Block.c, unit) node
    (* Align to the specified width *)
    | N_align: Location.t * int * label * label
               -> (Block.o, Block.c, unit) node
    (* Match the specified number of bits as padding.  The padding
       pattern is specified in the following N_collect_bits node *)
    | N_pad: Location.t * int * label * label
             -> (Block.o, Block.c, unit) node

    (* Collect matched bits from the marked position and check the
       specified predicate.  If it succeeds, N_collect_checked_bits
       assigns the collected bitvector to the specified variable, and
       jumps to the first label; otherwise, it fails to the second
       label.  N_check_bits does the same except that it does not
       assign the matched bits to any variable. *)
    | N_collect_checked_bits:
        Location.t * var * matched_bits_predicate * label * label
        -> (Block.o, Block.c, unit) node
    | N_check_bits:
        Location.t * matched_bits_predicate * label * label
        -> (Block.o, Block.c, unit) node

    (* forward jump: The label must be static. *)
    | N_jump: Location.t * label -> (Block.o, Block.c, unit) node

    (* return jump: The label must be virtual, indicating a successful
       return if to a success continuation, or an error return if to a
       failure continuation.  This is used to return from the CFG of
       a *user-defined* non-terminal.  Stdlib non-terminals are
       handled specially since they don't have a CFG. *)
    | N_return: Location.t * label -> (Block.o, Block.c, unit) node

    (* Constrained jump: the var should have been bound to the value
       of the constraint expression, and the label is the success
       continuation.  If the constraint fails (evaluates to false),
       rewind to the second label. *)
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
       first specified label.  A failure rewinds to the second label. *)
    | N_exec_dfa: dfa * var * label * label
                  -> (Block.o, Block.c, unit) node
    (* Special case for tag scanning. *)
    | N_scan: Location.t * (Ast.literal * Ast.scan_direction)
              * (*return*) var * label * label
              -> (Block.o, Block.c, unit) node

    (* Call the CFG for the specified non-terminal with the specified
       expressions for the inherited attributes.  On a successful
       continuation, continue at the first specified label.  The
       second label is the current failcont.
       At runtime: the labels specified in the node are the success
       and failure continuations, which get mapped to the virtual
       labels of the `nt_succcont` and `nt_failcont` for the
       non-terminal's CFG, as specified in its `nt_entry`. *)
    | N_call_nonterm:
        Anf.modul * Ast.ident * (Ast.ident * var) list * return * label * label
        -> (Block.o, Block.c, unit) node

  type entry_node  = (Block.c, Block.o, unit) node
  type linear_node = (Block.o, Block.o, unit) node
  type exit_node   = (Block.o, Block.c, unit) node

  let entry_label (type x v) (n: (Block.c, x, v) node) =
    match n with
      | N_label (_, l, _) -> l
      (* this should not be needed *)
      | _ -> assert false

  let successors (type e v) (n: (e, Block.c, v) node) =
    match n with
      | N_bits (_, _, sc, fl)
      | N_align (_, _, sc, fl)
      | N_pad (_, _, sc, fl)
      | N_collect_checked_bits (_, _, _, sc, fl)
      | N_check_bits (_, _, sc, fl)
      | N_constraint (_, _, sc, fl)
      | N_cond_branch (_, _, sc, fl)
      | N_exec_dfa (_, _, sc, fl)
      | N_scan (_, _, _, sc, fl)
      | N_call_nonterm (_, _, _, _, sc, fl)
        -> [raw_label_of sc; raw_label_of fl]
      | N_jump (_, l)
      | N_return (_, l)
        -> [raw_label_of l]
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
  {nt_name:      Ast.ident;
   (* each inherited attribute and the corresponding var used for it
      in the CFG *)
   nt_inh_attrs: (var * typ) StringMap.t;
   (* type of the return value after parsing this non-terminal *)
   nt_typ:       typ;
   (* the entry label for the CFG *)
   nt_entry:     Label.label; (* is implicitly static *)
   (* a pair of success and failure continuations are assumed for the
      CFG.  these need to mapped to the current runtime success and
      failure continuations during execution *)
   nt_succcont:  label;       (* must always be virtual *)
   nt_failcont:  label;       (* must always be virtual *)
   (* a successfully matched value will be bound to this variable *)
   nt_retvar:    var;
   (* all new vars allocated in the CFG for this non-terminal *)
   nt_used_vars: VSet.t;
   (* the location this non-term was defined *)
   nt_loc:       Location.t}

module ValueMap = Map.Make(struct type t = modul * string
                                  let compare = compare
                           end)

(* This is the complete set of CFG blocks in the specification,
   indexed by their entry label. *)
module LabelMap = Map.Make(LabelOrdSet)

(* The IR for the entire specification. *)
type spec_ir =
  {ir_gtoc:          nt_entry ValueMap.t; (* indexed by non-terminal name *)
   ir_blocks:        closed LabelMap.t;
   ir_statics:       opened; (* constants and functions *)
   ir_foreigns:      ffi_decl ValueMap.t;
   ir_init_failcont: label;  (* should always be virtual *)
   (* debugging state for the interpreter *)
   ir_tenv:          TypingEnvironment.environment;
   ir_venv:          VEnv.t}

(* The context for IR generation. *)
type context =
  {(* the typing environment *)
   ctx_tenv:     TypingEnvironment.environment;
   (* this will stay static during the construction of the IR *)
   ctx_gtoc:     nt_entry ValueMap.t;
   (* this will be updated during the construction with completed
      blocks *)
   ctx_ir:       closed LabelMap.t;
   (* the current variable environment *)
   ctx_venv:     VEnv.t;
   (* the current failure continuation *)
   ctx_failcont: label; (* may be static or virtual *)
   (* intermediate re forms for regexp non-terminals *)
   ctx_re_env:   re_env;
   (* whether the current mode is bit-wise *)
   ctx_bitmode:  bool}

type error =
  | Unbound_return_expr
  | Unsupported_construct of string
  | Nonterm_variable_required of Ast.ident

exception Error of Location.t * error

let error_msg = function
  | Unbound_return_expr ->
      "The return expression in this action block is not used."
  | Unsupported_construct s ->
      Printf.sprintf "IR generation for `%s' is currently unsupported." s
  | Nonterm_variable_required ntd ->
      Printf.sprintf "Non-terminal `%s' requires a variable to indicate the matched value."
        (Location.value ntd)
