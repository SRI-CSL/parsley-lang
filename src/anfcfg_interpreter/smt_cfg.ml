open Parsing
(* open Typing open Flow *)
open Anfcfg.Anf
open Anfcfg.Dfa
open Anfcfg.Cfg
(* open Values *)

type smtBool = string
type smtString = string
type smtConstraintString = string

let print_dfa _ : string = "TODO: print_dfa";

module SMTValue = struct
  type value =
    | V_value of value * string
    | V_unit
    | V_bool of bool
    | V_bit of bool
    | V_char of char (* also used for byte *)
    | V_int of Parsing.Ast.num_t * Int64.t
    | V_float of float
    | V_string of string
    | V_bitvector of bool list                (* big-endian *)
    | V_option of value option
    | V_list of value list
    | V_tuple of value list
    | V_constr of constr * value list
    | V_record of (string * value) list
    (* module types *)
    | V_set of value list
    | V_map of (value * value) list
end

(* The node structure of the CFG for SMT constraint generation *)
module SMTNode = struct
  type node =
    (* Constraint to match a specified number of bits *)
    | N_bits_constraint: Location.t * int * label * label -> node
    (* Constraint to align to the specified width *)
    | N_align_constraint: Location.t * int * label * label -> node
    (* Constraint to match the specified number of bits as padding.  The
       padding pattern is specified in the following N_collect_bits node *)
    | N_pad_constraint: Location.t * int * label * label -> node

    (* Collect matched bits from the marked position and check the
       specified predicate.  If it succeeds, N_collect_checked_bits
       assigns the collected bitvector to the specified variable, and
       jumps to the first label; otherwise, it fails to the second
       label.  N_check_bits does the same except that it does not
       assign the matched bits to any variable. *)
    | N_collect_checked_bits_constraint:
        Location.t * var * matched_bits_predicate * label * label -> node

    | N_check_bits_constraint:
        Location.t * matched_bits_predicate * label * label -> node

    | N_constraint_jump_constraint: Location.t * var * label * label -> node

    | N_cond_branch_constraint: Location.t * var * label * label -> node

    | N_dfa_constraint: Location.t * dfa * var * label * label -> node

    (* Special case for tag scanning. *)
    | N_scan_constraint: Location.t * (Ast.literal * Ast.scan_direction)
              * (*return*) var * label * label -> node

    | N_value: SMTValue.value -> node
    | N_unit
    | N_record: (string * node) list -> node

    (* Call the CFG for the specified non-terminal with the specified
       expressions for the inherited attributes.  On a successful
       continuation, continue at the first specified label.  The
       second label is the current failcont.
       At runtime: the labels specified in the node are the success
       and failure continuations, which get mapped to the virtual
       labels of the `nt_succcont` and `nt_failcont` for the
       non-terminal's CFG, as specified in its `nt_entry`. *)
    | N_call_nonterm_constraint:
        Anfcfg.Anf.modul * Ast.ident * (Ast.ident * var) list * return * label * label
        -> node

  let successors (n: node) =
    match n with
      | N_bits_constraint (_, _, sc, fl)
      | N_align_constraint (_, _, sc, fl)
      | N_pad_constraint (_, _, sc, fl)
      | N_collect_checked_bits_constraint (_, _, _, sc, fl)
      | N_check_bits_constraint (_, _, sc, fl)
      | N_constraint_jump_constraint (_, _, sc, fl)
      | N_cond_branch_constraint (_, _, sc, fl)
      | N_dfa_constraint (_, _, _, sc, fl)
      | N_scan_constraint (_, _, _, sc, fl)
      | N_call_nonterm_constraint (_, _, _, _, sc, fl)
        -> [raw_label_of sc; raw_label_of fl]
      | N_record _
      | N_unit
      | N_value _ -> []
      (* this should not be needed *)
      (* | _ -> assert false *)
end

(*
let epsilon_rule (f: smtBool) (v: smtString) (s: smtString) (p: smtString) (r: smtString) : smtConstraintString =
";; epsilon rule
(define-fun epsilonrule ((" ^ f ^ " Bool) (" ^ v ^ " String) (" ^ s ^" String) (" ^ p ^" String) (" ^ r ^ " String))
Bool
(and
  " ^ f ^"
  (str.in.re " ^ p ^" (re.++ (str.to.re "") (re.* re.allchar)))
  (= " ^ v ^" "")
  (= " ^ s ^ " (str.++ " ^ p ^ " " ^ r ^ ")))
";
*)
