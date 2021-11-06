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
(*  Copyright (C) 2006. Fran�ois Pottier, Yann R�gis-Gianas               *)
(*  and Didier R�my.                                                      *)

(** This module provides a simple pretty-printer for the terms
    maintained by a unifier.

    We follow the convention that types and type schemes are represented
    using the same data structure. In the case of type schemes, universally
    quantified type variables are distinguished by the fact that their rank
    is [none]. The pretty-printer binds these variables locally, while other
    (non-quantified) type variables are considered part of a global namespace.
*)

open TypeAlgebra
open CoreAlgebra
open MultiEquation

(** [name_from_int i] turns the integer [i] into a type variable name. *)
let rec name_from_int i =
  if i < 26
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
type arg =
  Arg of (MultiEquation.variable  (* type or type operator *)
          * string                (* print name *)
          * arg list              (* syntax for type arguments *)
          * bool                  (* whether type operator is infix *)
          * associativity
          * bool)                 (* parentheses for disambiguation *)

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

  let var_name v =
    let desc = UnionFind.find v in
    let autoname () =
      let prefix, c, h =
        if is_type_scheme && IntRank.compare desc.rank IntRank.none = 0
        then "'", i, history
        else "''", gi, ghistory in
      try
        snd (List.find (fun (v', _) -> UnionFind.equivalent v v') !h)
      with Not_found ->
        incr c;
        let result = prefix ^ name_from_int !c in
        desc.name <- Some (TName result);
        h := (v, result) :: !h;
        result in
    (match desc.name with
       | Some (TName name) ->
           if desc.kind <> Constant then
             try
               Misc.assocp (UnionFind.equivalent v) !history
             with Not_found ->
               history := (v, name) :: !history;
               name
           else name
       | _ -> autoname ())
    (* ^ ("["^string_of_int desc.rank^"]") *)
    (* ^ (match desc.kind with Constant -> "#" | Rigid -> "!" | Flexible -> "?") *)
  in

  (* Term traversal. *)
  let rec print_variable v =
    let is_hit v =
      Mark.same (UnionFind.find v).mark hit
    and is_visited v =
      Mark.same (UnionFind.find v).mark visiting in
    let var_or_sym v =
      (match variable_name v with
         | Some (TName name) ->
             (* If this is a builtin symbol, use the given name, else
                generate a possibly decorated name. *)
             (match as_symbol (TName name) with
                | Some sym ->
                    (v, name, [], infix sym, associativity sym, false)
                | None ->
                    (v, var_name v, [], false, Assoc_none, false))
         | None ->
             (v, var_name v, [], false, Assoc_none, false)) in
    let desc = UnionFind.find v in
    (* If this variable was visited already, we mark it as ``hit
       again'', so as to record the fact that we need to print an
       equation at that node when going back up. *)
    if is_hit v || is_visited v then
      begin
        desc.mark <- hit;
        var_or_sym v
      end

    (* If this variable was never visited, we mark it as ``being
       visited'' before processing it, so as to detect cycles.
       If, when we are done with this variable, its mark has
       changed to ``hit again'', then it must be part of a cycle,
       and we annotate it with an inline equation. *)
    else begin
      desc.mark <- visiting;
      match desc.structure with
        | None ->
            var_or_sym v
        | Some t ->
            let (v', name, args, infix, assoc, p) as r =
              print_term t in
            if is_hit v
            then let vname = var_name v in
                 (v, vname ^ " =",
                  [ Arg (v', name, args, infix, assoc, p) ],
                  false, assoc, true)
            else (desc.mark <- Mark.none; r)
    end

  and print_term t =
    let at_left  = function [] -> true | [ _x ] -> false | _ -> assert false
    and at_right = function [] -> true | [ _x ] -> false | _ -> assert false
    and is_enclosed = function Assoc_enclosed _ -> true  | _ -> false in
    let print = function
      | App (t1, t2) ->
          let (op1, name1, args1, infix1, assoc1, force_paren1) =
            print_variable t1
          and (op2, name2, args2, infix2, assoc2, force_paren2) =
            print_variable t2 in
          let priority name =
            match as_symbol name with
              | Some sym -> priority sym
              | None     -> -1 in
          let paren_t2 =
            force_paren2 ||
              if are_equivalent op1 op2
              then let _ = assert (assoc1 = assoc2) in
                   (assoc2 = Assoc_left && at_right args2)
                   || (assoc2 = Assoc_right && at_left args1)
              else (not (is_enclosed assoc2))
                   && (priority (TName name2) > priority (TName name1)) in
          (op1, name1,
           (args1 @ [ Arg (op2, name2, args2, infix2, assoc2, paren_t2)]),
           infix1, assoc1, force_paren1)
      | Var v ->
          print_variable v
    in print t in

  let prefix () =
    if is_type_scheme
    then match !history with
           | [] ->
               ""
           | history ->
               List.fold_left
                 (fun quantifiers (v, _) -> quantifiers ^ " " ^ (var_name v))
                 "forall" (List.rev history)
               ^ ". "
    else "" in

  let as_string f r =
    let rec loop (Arg (_, name, args, infix, assoc, is_paren)) =
      if args = []
      then name
      else paren is_paren
             (if infix
              then Misc.print_separated_list (" " ^ name ^ " ") loop args
              else let pref, sep, suff =
                     match assoc with
                       | Assoc_enclosed (b, e) ->
                           b, ", ", " " ^ e
                       | _ ->
                           if List.length args > 0
                           then (name ^ "<"), ", ", " >"
                           else name, " ", "" in
                   pref
                   ^ (if args <> [] then " " else "")
                   ^ (Misc.print_separated_list sep loop args)
                   ^ suff) in
    let (op, name, args, infix, assoc, _) = f r in
    prefix () ^ loop (Arg (op, name, args, infix, assoc, false)) in

  (as_string print_variable, as_string print_term)

let print_term b t =
  let t = explode t in
  (snd (printer b)) t

let print_variable b v =
  (fst (printer b)) v
