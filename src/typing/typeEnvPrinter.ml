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

(*  Adapted from:                                                         *)
(*  Mini, a type inference engine based on constraint solving.            *)
(*  Copyright (C) 2006. François Pottier, Yann Régis-Gianas               *)
(*  and Didier Rémy.                                                      *)

(** This module provides a simple pretty-printer for the terms
    maintained by a unifier.

    We follow the convention that types and type schemes are represented
    using the same data structure. In the case of type schemes, universally
    quantified type variables are distinguished by the fact that their rank
    is [none]. The pretty-printer binds these variables locally, while other
    (non-quantified) type variables are considered part of a global namespace.
*)

open Parsing
open TypeAlgebra
open CoreAlgebra
open MultiEquation

(** [name_from_int i] turns the integer [i] into a type variable name. *)
let rec name_from_int i =
  if   i < 26
  then String.make 1 (Char.chr (0x61 + i))
  else name_from_int (i / 26 - 1) ^ name_from_int (i mod 26)

(** [gi] is the last consumed number. *)
let gi = ref (-1)

(** [ghistory] is a mapping from variables to variable names. *)
let ghistory = ref []

(** [reset()] clears the global namespace, which is implemented
    by [gi] and [ghistory]. *)
let reset () =
  gi := -1;
  ghistory := []

(** printing syntax for a type or type operator *)
type print_info =
  MultiEquation.variable     (* type or type operator *)
  * Ast.full_tname           (* name *)
  * arg list                 (* syntax for type arguments *)
  * bool                     (* whether type operator is infix *)
  * associativity
  * bool                     (* parentheses for disambiguation *)

and arg =
  Arg of print_info

type type_info =
    (MultiEquation.variable * string) list (* forall quantifiers *)
  * print_info

let paren b e = if b then "(" ^ e ^ ")" else e

(** [print is_type_scheme v] returns a printable representation of
    the type or type scheme whose entry point is [v]. The parameter
    [is_type_scheme] tells whether [v] should be interpreted as a
    type or as a type scheme. Recursive types are dealt with by
    printing inline equations. Consecutive calls to [print] share
    the same variable naming conventions, unless [reset] is called
    in between. *)
let printer is_type_scheme =
  (* Create marks to deal with cycles. *)
  let visiting = Mark.fresh()
  and hit = Mark.fresh() in

  (* Create a local namespace for this type scheme. *)
  let i = ref (-1)
  and history = ref [] in

  (* [var_name v] looks up or assigns a name to the variable [v]. When
     dealing with a type scheme, then the local or global namespace
     is used, depending on whether [v] is universally quantified or
     not. When dealing with a type, only the global namespace is
     used. *)

  let var_name v : Ast.full_tname =
    let desc = UnionFind.find v in
    let autoname () =
      let prefix, c, h =
        if   is_type_scheme && IntRank.compare desc.rank IntRank.none = 0
        then "'", i, history
        else "''", gi, ghistory in
      match List.find_opt (fun (v', _) -> UnionFind.equivalent v v') !h with
        | Some (_, x) -> x
        | None        -> incr c;
                         let result = prefix ^ name_from_int !c in
                         desc.name <- Some (AstUtils.stdlib, TName result);
                         h := (v, result) :: !h;
                         result in
    (match desc.name with
       | Some (m, TName name) when m = AstUtils.stdlib ->
           if   desc.kind <> Constant
           then try  AstUtils.stdlib, TName (Misc.assocp (UnionFind.equivalent v) !history)
                with Not_found -> history := (v, name) :: !history;
                                  AstUtils.stdlib, TName name
           else AstUtils.stdlib, TName name
       | Some (m, name) ->
           (* We should not have module-qualified type variables. *)
           assert (desc.kind = Constant);
           m, name
       | _ -> AstUtils.stdlib, TName (autoname ()))
    (* ^ ("["^string_of_int desc.rank^"]") *)
    (* ^ (match desc.kind with Constant -> "#" | Rigid -> "!" | Flexible -> "?") *)
  in

  let str_of_name (m, Ast.TName n) =
    (AstUtils.mk_modprefix m) ^ n in

  (* Term traversal. *)
  let rec variable_info v : print_info =
    let is_hit v =
      Mark.same (UnionFind.find v).mark hit
    and is_visited v =
      Mark.same (UnionFind.find v).mark visiting in
    let var_or_sym v =
      match variable_name v with
        | Some (md, name) ->
            (* If this is a builtin symbol, use the given name, else
               generate a possibly decorated name. *)
            (match as_symbol (md, name) with
               | Some sym ->
                   (v, (md, name), [], infix sym, associativity sym, false)
               | None ->
                   (v, var_name v, [], false, Assoc_none, false))
        | None ->
            (v, var_name v, [], false, Assoc_none, false) in
    let desc = UnionFind.find v in
    (* If this variable was visited already, we mark it as ``hit
       again'', so as to record the fact that we need to print an
       equation at that node when going back up. *)
    if   is_hit v || is_visited v
    then (desc.mark <- hit;
          var_or_sym v)

    (* If this variable was never visited, we mark it as ``being
       visited'' before processing it, so as to detect cycles.
       If, when we are done with this variable, its mark has
       changed to ``hit again'', then it must be part of a cycle,
       and we annotate it with an inline equation. *)
    else (desc.mark <- visiting;
          match desc.structure with
            | None ->
                var_or_sym v
            | Some t ->
                let (v', name, args, infix, assoc, p) as r =
                  term_info t in
                if   is_hit v
                then let m, TName vname = var_name v in
                     (v, (m, TName (vname ^ " =")),
                      [ Arg (v', name, args, infix, assoc, p) ],
                      false, assoc, true)
                else (desc.mark <- Mark.none; r))

  and term_info t : print_info =
    let at_left     = function [] -> true | [ _x ] -> false | _ -> assert false
    and at_right    = function [] -> true | [ _x ] -> false | _ -> assert false
    and is_enclosed = function Assoc_enclosed _ -> true  | _ -> false in
    let info = function
      | App (t1, t2) ->
          let (op1, name1, args1, infix1, assoc1, force_paren1) =
            variable_info t1
          and (op2, name2, args2, infix2, assoc2, force_paren2) =
            variable_info t2 in
          let priority name =
            match as_symbol name with
              | Some sym -> priority sym
              | None     -> -1 in
          let paren_t2 =
            force_paren2 ||
              if   are_equivalent op1 op2
              then let _ = assert (assoc1 = assoc2) in
                   (assoc2 = Assoc_left && at_right args2)
                   || (assoc2 = Assoc_right && at_left args1)
              else (not (is_enclosed assoc2))
                   && (priority name2 > priority name1) in
          (op1, name1,
           (args1 @ [Arg (op2, name2, args2, infix2, assoc2, paren_t2)]),
           infix1, assoc1, force_paren1)
      | Var v ->
          variable_info v
    in info t in

  let prefix () =
    if   is_type_scheme
    then match !history with
           | [] ->
               ""
           | history ->
               List.fold_left
                 (fun quantifiers (v, _) ->
                   quantifiers ^ " " ^ (str_of_name (var_name v)))
                 "forall" (List.rev history)
               ^ ". "
    else "" in

  let as_string f r : string =
    let rec loop (Arg (_, name, args, infix, assoc, is_paren)) =
      let sname = str_of_name name in
      if   args = []
      then sname
      else paren is_paren
             (if   infix
              then Misc.print_separated_list (" " ^ sname ^ " ") loop args
              else let pref, sep, suff =
                     match assoc with
                       | Assoc_enclosed (b, e) ->
                           b, ", ", e
                       | _ ->
                           if   List.length args > 0
                           then (sname ^ "<"), ", ", " >"
                           else sname, "", "" in
                   pref
                   ^ (Misc.print_separated_list sep loop args)
                   ^ suff) in
    let (op, name, args, infix, assoc, _) = f r in
    prefix () ^ loop (Arg (op, name, args, infix, assoc, false)) in

  let as_info f r : type_info =
    let info = f r in
    let quantifiers = if   is_type_scheme
                      then !history
                      else [] in
    (quantifiers, info) in

  (as_string variable_info, as_string term_info),
  (as_info   variable_info, as_info   term_info)

let print_variable b v =
  (fst (fst (printer b))) v

let print_term b t =
  let t = explode t in
  (snd (fst (printer b))) t

let variable_type_info b v =
  (fst (snd (printer b))) v

let term_type_info b t =
  let t = explode t in
  (snd (snd (printer b))) t
