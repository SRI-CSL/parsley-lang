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
open Ast
open Typing
open Anf

(* Based on the algorithm in
   'Compiling pattern matching to good decision trees', by Luc Maranget.
   Proceedings of the 2008 ACM SIGPLAN workshop on ML, September 2008
   https://doi.org/10.1145/1411304.1411311

   The representation of occurrence sequences is reversed from that
   implied in the paper.  This is to ease interpretation and execution,
   where a term is traversed from the root to the sub-term. This is
   simpler if the occurrence is represented in the same order.
 *)

(* pattern action row *)
type prow = pat list * int
(* pattern action matrix *)
type pmat = prow list

(* constructor of a type, or wildcard *)
type con =
  | Con of constr * (* arity *) int
  | Lit of Ast.primitive_literal
  | Default

(* intermediate form for pattern match compilation *)
type decision_tree =
  | Leaf of int
  | Switch of occurrence * (con * typ * Location.t * decision_tree) list

let specialize = Pattern_utils.specialize_mat
let default (m: pmat) = Pattern_utils.default_mat m

(* printers *)

let sprint_con = function
  | Con (c, a) ->
      Printf.sprintf "%s(#%d)" (string_of_constr c) a
  | Lit l ->
      Printf.sprintf "Lit (%s)" (AstPrinter.string_of_literal l)
  | Default ->
      "*"

let pp_string    = AstPrinter.pp_string
let pp_open_vbox = AstPrinter.pp_open_vbox
let pp_close_box = AstPrinter.pp_close_box
let pp_break     = AstPrinter.pp_break
let pp_cut       = AstPrinter.pp_cut
let pp_flush     = AstPrinter.pp_flush

let sprint_occ occ =
  "[" ^ (String.concat " "
           (List.map string_of_int occ)) ^ "]"

let print_dectree d =
  let rec pr_dectree d =
    match d with
      | Leaf d ->
          pp_string (Printf.sprintf "Leaf %d" d)
      | Switch (occ, cases) ->
          pp_string ("occ:" ^ (sprint_occ occ) ^ "(");
          pp_open_vbox 0;
          List.iteri pr_case cases;
          pp_close_box ();
          pp_string ")"
  and pr_case idx (c, _, _, d) =
    let s = Printf.sprintf " %d| %s => (" idx (sprint_con c) in
    pp_string s;
    pr_dectree d;
    pp_string ")";
    pp_cut ()
  in pr_dectree d;
     pp_flush ()

let print_pmat m =
  let auxp = AstPrinter.mk_auxp_typed (fun _ -> "") in
  let prow (r, d) =
    pp_string (Printf.sprintf " [%d: " d);
    List.iter (fun p ->
        AstPrinter.print_pattern auxp p;
        pp_string " "
      ) r;
    pp_string "] ";
    pp_break 0 0 in
  pp_open_vbox 2;
  pp_break 0 0;
  List.iter prow m;
  pp_close_box ();
  pp_flush ()


(* decision tree computation *)

(* checks if a pattern row is effectively a default row *)
let rec is_default_row = function
  | [] ->
      true
  | {pattern = P_wildcard; _} :: rest
  | {pattern = P_var _; _}    :: rest ->
      is_default_row rest
  | _ ->
      false

let conarg_paths arity root_path =
  let rec helper acc i =
    if   i = 0
    then acc
    else helper ((root_path @ [i]) :: acc) (i - 1) in
  helper [] arity

(* The input to the decision tree constructor includes
   [m]:     the current pattern-action matrix
   [paths]: the path for each pattern column of the matrix
 *)
let rec to_dectree (tenv: TypingEnvironment.environment)
          (m: pmat) (paths: occurrence list)
        : decision_tree =
  match m with
    | [] ->
        (* This should never be seen at the top-level, since the empty
           matrix has no actions and hence no possible decision
           result. *)
        assert false
    | (prow, a) :: _ ->
        assert (List.length prow = List.length paths);
        (if   is_default_row prow
         then Leaf a
         else
           (* The naive column selection just uses the first column as
              the next scrutinee; this avoids the need for the Swap
              decision tree.
              TODO: add Swap, and employ heuristics to pick the best
              column. *)
           let col    = Pattern_utils.first_col m in
           let heads  = Pattern_utils.roots tenv col in
           let path   = List.hd paths in
           let rpaths = List.tl paths in
           match heads with
             | [] ->
                 (* Naive column selection will often give a column
                    with no heads. *)
                 let def = default m in
                 (match def with
                    | [] -> Leaf a (* last col with only wildcards *)
                    | _  -> to_dectree tenv def rpaths)
             | ({pattern_aux = def_typ; pattern_loc = def_loc; _}, _) :: _ ->
                 let switches =
                   List.map (fun (h, ar) ->
                       let s = specialize tenv m h in
                       let paths = (conarg_paths ar path) @ rpaths in
                       let dt = to_dectree tenv s paths in
                       match h.pattern with
                         | P_wildcard | P_var _ ->
                             (* wildcards are not head constructors *)
                             assert false
                         | P_literal l ->
                             Lit l, h.pattern_aux, h.pattern_loc, dt
                         | P_variant (c, _) ->
                             let c = convert_con c in
                             Con (c, ar), h.pattern_aux, h.pattern_loc, dt
                     ) heads in
                 if   Pattern_utils.is_complete_sig tenv (fst (List.split heads))
                 then Switch (path, switches)
                 else (* add the default case *)
                   let def = default m in
                   (* see above explanation for handling the ~~ operator *)
                   (match def with
                      | [] ->
                          Leaf a
                      | _  ->
                          let dt =
                            to_dectree tenv def rpaths in
                          Switch (path, (switches @ [(Default, def_typ, def_loc, dt)])))
        )

let to_decision_tree tenv pmat _loc =
  (* seed with the root occurrence *)
  to_dectree tenv pmat [root_occurrence]

(* computes the path occurrences for each pattern variable *)
let pvar_paths (p: pat)
    : (TypeInfer.varid Ast.var * typ * occurrence) list =
  let rec helper acc p path =
    match p.pattern with
      | P_wildcard | P_literal _ ->
          acc
      | P_var v ->
          (v, p.pattern_aux, path) :: acc
      | P_variant (_, ps) ->
          let acc, _ =
            List.fold_left (fun (acc, i) p ->
                let acc = helper acc p (path @ [i]) in
                acc, i + 1
              ) (acc, 1) ps in
          acc in
  (* start with the occurrence for the root path *)
  helper [] p []
