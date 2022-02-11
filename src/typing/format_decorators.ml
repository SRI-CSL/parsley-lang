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

(* processing of format decorators *)

open Parsing
open Ast
open TypingExceptions

module StringSet = Set.Make(String)

let display_decorated = ref StringSet.empty

type deco_value = ident * deco_arg list

(* Check decorator usage satisfies the following:
   . any decorator should have a single use
   . any decorator key should appear only once
 *)
let pre_check_format_decorator =
  let check_keys a args =
    List.fold_left (fun s kv ->
        match kv with
          | Deco_key k | Deco_keyvalue (k, _) ->
              let ks = Location.value k in
              if StringSet.mem ks s
              then raise (Error (Location.loc k, RepeatedDecoratorKey (a, k)))
              else StringSet.add ks s
          ) StringSet.empty args in
  let check_deco s a =
    let at = a.deco_type in
    let ats = Location.value at in
    if StringSet.mem ats s
    then raise (Error (Location.loc at, RepeatedDecoratorType at))
    else (ignore (check_keys a.deco_value a.deco_args);
          StringSet.add ats s) in
  function
  | None ->
      ()
  | Some decos ->
      ignore (List.fold_left check_deco StringSet.empty decos)

(* Find the value of a specified decorator type *)
let lookup_decorator_value (name: string) (odecos: decorator list option)
    : deco_value option =
  match odecos with
    | None ->
        None
    | Some ats ->
        let nas = List.filter_map
                    (fun a ->
                      let atn = Location.value a.deco_type in
                      if name = atn
                      then Some (a.deco_value, a.deco_args)
                      else None
                    ) ats in
        (* We checked for uniqueness above *)
        assert (List.length nas = 1);
        Some (List.hd nas)

(* Convert a decorator value into a non-terminal instance, using
   the following rules:

   . the name of the decorator value needs to be upper-case, as for
     non-terminals

   . every decorator key should specify a value, as required for
     inherited attributes of non-terminals

   . each value should either be boolean ('true'/'false').  This
     restriction does not affect current use-cases, but may be relaxed
     if needed.

     The rationale for this restriction is that it allows
     us to enumerate all the ways the non-terminal can be
     instantiated.  For example, if the non-terminal is a regexp
     non-terminal with multiple possible rules (e.g. whitespace), we
     could constant-fold to compute the regexp corresponding to each
     call of this non-terminal.
 *)

(* Perform the conversion described above, and return an untyped
   non-term node. *)
let non_term_of_decorator_value (deco: deco_value)
    : (unit, unit) non_term_instance =
  let mk_bool s loc =
    let bool = Location.mk_loc_val "bool" loc in
    let v = E_constr ((bool, Location.mk_loc_val s loc), []) in
    AstUtils.make_expr_loc v loc in
  let n, args = deco in
  if not (AstUtils.is_valid_nonterm_name (Location.value n))
  then raise (Error (Location.loc n, InvalidDecoratorName n));
  let iattrs =
    match args with
      | [] ->
          None
      | _::_ ->
          let ia =
            List.fold_left (fun acc a ->
                match a with
                  | Deco_key k ->
                      let err = UnvaluedDecoratorKey (n, k) in
                      raise (Error (Location.loc k, err))
                  | Deco_keyvalue (k, v) ->
                      let vs = Location.value v in
                      let loc = Location.loc v in
                      let av = match vs with
                          | "true" ->
                              k, A_eq, mk_bool "True" loc
                          | "false" ->
                              k, A_eq, mk_bool "False" loc
                          | _ ->
                              let err =
                                InvalidDecoratorKeyValue (n, k, v) in
                              raise (Error (Location.loc v, err)) in
                      av :: acc
              ) [] args in
          Some (List.rev ia) in
  n, iattrs

(* helpers to check format decorators *)
let get_whitespace_nonterm deco =
  match lookup_decorator_value "whitespace" deco with
    | None ->
        None
    | Some a ->
        Some (non_term_of_decorator_value a)

(* top-level check on decorators *)
let check_decorator deco =
  pre_check_format_decorator deco;
  (* Currently, the only supported decorator is 'whitespace'.  If
     specified, it should name a valid non-terminal. *)
  ignore (get_whitespace_nonterm deco)

(* This decorator results in all the rules of the non-terminal being
   pre-processed to insert the specified whitespace token at
   appropriate points between the elements of each production rule of
   the non-terminal.

   This process follows some heuristics listed below.  The intent for
   the heuristics are to be simple (involve looking at only local
   information about the rule), and to be relatively easy to explain
   to the user.  For full control, the user can avoid using the
   whitespace decorator.

   The goal is to allow the most common use cases to be addressed
   without excessive verbosity; i.e. when no bit-level or view
   constructions or cursor-dependent computations are used, the result
   should be equivalent to a conventional text-based parser.
 *)
let fixup_for_whitespace (ntd: (unit, unit) non_term_defn)
      (ws: (unit, unit) non_term_instance)
    : (unit, unit) non_term_defn =
    (* Inspect the gap between two consecutive rule elements and
       insert the whitespace token in the gap provided:

       . It is not inserted immediately before or after a bit-level
         element, since these elements rely crucially on byte
         alignment.

       . If the sub-element named by a bound (i.e. named) element is
         atomic (i.e. not under another combinator), the atomic
         element is left intact, since whitespace insertion can affect
         the bound value.

         The rationale for this is the principle of least surprise.
         The user typically does not want a bound value for a match
         to include any surrounding whitespace, especially
         whitespace that results from an automatic insertion by the
         compiler.

         If the sub-element is complex (under a combinator),
         whitespace is also not inserted under the combinator.
         This is motivated by a different flavor of the same
         least-surprise principle: the insertion changes the type of
         the binding variable, resulting in a type that may not match
         the rule structure as written, and thus causing user
         consternation.

       . It is not inserted before an action or a constraint
         (since they may compute cursor locations or views).

         The rationale here is any computations performed within the
         constraint or action that rely directly or indirectly on
         cursor locations should not be perturbed by the introduction
         of whitespace.

       . Similarly, it is not inserted before any view control
         elements.

         The views computed by or operated on by the view control
         elements should not be perturbed by local whitespace
         insertion.

         The rule elements inside the view control elements are also
         left intact, since view control is typically used for
         offset-sensitive parsing and may be sensitive to whitespace
         introduction.

       . It is not inserted before the first element of a sequence,
         but may be inserted after the last element provided the other
         rules are satisfied.

         This means that if this sequence is the argument of a star or
         repeat combinator, there cannot be more than one inserted
         whitespace token  at the junction of two repetitions of the
         sequence.

       . If the argument of a star or option is atomic, whitespace is
         not inserted before or after that argument.  That is, any
         atomic argument of these combinators is left intact.  (Note
         that whitespace may be inserted before or after the
         combinator itself.)

       . Similarly, it leaves any atomic argument of the choice
         combinator intact.  However, each argument of the choice
         operator is processed independently of the others.  That is,
         if the choice combinator has some atomic and some complex
         arguments, whitespace may be inserted within the complex
         arguments.

       All these rules mainly control when whitespace tokens _cannot_
       be automatically inserted.  It follows that they are inserted
       whenever none of the above rules are violated.

     *)
  let rec is_bit_level_elem re =
    match re.rule_elem with
      | RE_bitvector _ | RE_align _ | RE_pad _ | RE_bitfield _ ->
          true
      | RE_named (_, re) | RE_star (re, _) | RE_opt re ->
          is_bit_level_elem re
      | RE_choice alts ->
          List.exists is_bit_level_elem alts
      (* FIXME: this does not handle the case when a non-term is purely
         bit-level *)
      | RE_non_term _ ->
          false
      | _ ->
          false in
  let rec is_view_control_elem re =
    match re.rule_elem with
      | RE_set_view _ | RE_at_pos _ | RE_at_view _ | RE_map_views _ ->
          true
      | RE_named (_, re) ->
          is_view_control_elem re
      | _ ->
          false in
  let mk_start_loc loc =
    let pos = Location.get_start loc in
    Location.mk_loc pos pos in
  let rec process_elems ws_allowed prev_loc acc elems =
    let mk_insert_loc ploc cloc =
      Location.mk_loc (Location.get_end ploc) (Location.get_start cloc) in
    let mk_ws_elem loc =
      {rule_elem = RE_non_term ws;
       rule_elem_loc = loc;
       rule_elem_aux = ()} in
    let next_acc iloc =
      if ws_allowed
      then (mk_ws_elem iloc) :: acc
      else acc in
    match elems  with
      | [] ->
          let e = Location.get_end prev_loc in
          let loc = Location.mk_loc e e in
          List.rev (next_acc loc)
      | re :: rest when is_bit_level_elem re ->
          process_elems false re.rule_elem_loc (re :: acc) rest
      | re :: rest when is_view_control_elem re ->
          process_elems true re.rule_elem_loc (re :: acc) rest
      | ({rule_elem = RE_constraint _; _} as re) :: rest
      | ({rule_elem = RE_action _; _} as re) :: rest ->
          process_elems true re.rule_elem_loc (re :: acc) rest
      | ({rule_elem = RE_named _; _} as re) :: rest ->
          let iloc = mk_insert_loc prev_loc re.rule_elem_loc in
          let acc = next_acc iloc in
          process_elems true re.rule_elem_loc (re :: acc) rest
      | ({rule_elem = RE_seq res; _} as re) :: rest
      | ({rule_elem = RE_seq_flat res; _} as re) :: rest ->
          let res = process_elems false prev_loc [] res in
          let re = {re with rule_elem = RE_seq res} in
          let iloc = mk_insert_loc prev_loc re.rule_elem_loc in
          let acc = next_acc iloc in
          (* if we inserted ws at the end of res, then don't insert
             it again after this element.  if we didn't for some
             reason, then that reason should apply at this point too
             (check this!), so don't insert it.  either way, we flag
             as don't insert. *)
          process_elems false re.rule_elem_loc (re :: acc) rest
      | ({rule_elem = RE_choice alts; _} as re) :: rest ->
          let re =
            {re with
              rule_elem = RE_choice (List.map process_elem alts)} in
          (* disallow ws after this element using same reasoning as
             for RE_seq *)
          process_elems false re.rule_elem_loc (re :: acc) rest
      | ({rule_elem = RE_star (re', bnd); _} as re) :: rest ->
          let re' = process_elem re' in
          let re = {re with rule_elem = RE_star (re', bnd)} in
          let iloc = mk_insert_loc prev_loc re.rule_elem_loc in
          let acc = next_acc iloc in
          process_elems true re.rule_elem_loc (re :: acc) rest
      | ({rule_elem = RE_opt re'; _} as re) :: rest ->
          let re' = process_elem re' in
          let re = {re with rule_elem = RE_opt re'} in
          let iloc = mk_insert_loc prev_loc re.rule_elem_loc in
          let acc = next_acc iloc in
          process_elems true re.rule_elem_loc (re :: acc) rest
      (* non-special cases below *)
      | re :: rest ->
          let iloc = mk_insert_loc prev_loc re.rule_elem_loc in
          let acc = next_acc iloc in
          process_elems true re.rule_elem_loc (re :: acc) rest
  and process_elem re =
    let ploc = mk_start_loc re.rule_elem_loc in
    (* descend under non-view non-regexp combinators, leaving others intact *)
    match re.rule_elem with
      | RE_seq res ->
          {re with rule_elem = RE_seq (process_elems false ploc [] res)}
      | RE_choice alts ->
          {re with
            rule_elem = RE_choice (List.map process_elem alts)}
      | RE_star (re', bnd) ->
          {re with rule_elem = RE_star (process_elem re', bnd)}
      | RE_opt re' ->
          {re with rule_elem = RE_opt (process_elem re')}
      | RE_seq_flat res ->
          {re with rule_elem = RE_seq_flat (process_elems false ploc [] res)}
      | _ ->
          re in
  let process_rule r =
    let loc = mk_start_loc r.rule_loc in
    {r with rule_rhs =
              process_elems true loc [] r.rule_rhs} in
  let ntd =
    {ntd with non_term_rules =
                List.map process_rule ntd.non_term_rules} in
  let n = Location.value ntd.non_term_name in
  if StringSet.mem n !display_decorated
  then (AstPrinter.print_nterm_defn (fun _ -> "") ntd;
        AstPrinter.pp_flush ();
        Printf.printf "\n");
  ntd
