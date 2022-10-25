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

module TEnv = TypingEnvironment
module TExc = TypingExceptions

let mk_full_tname m t =
  m, TName (Location.value t)

(* Expands type abbreviations in a type expression. *)
let expand_type_abbrevs env te =
  let rec expand te =
    let loc = te.type_expr_loc in
    match te.type_expr with
      | TE_tvar _ ->
          te
      | TE_tname (m, t) ->
          let tc = mk_full_tname m t in
          (match TEnv.lookup_type_abbrev env tc with
             | None -> te
             | Some abb ->
                 let n = List.length abb.TEnv.type_abbrev_tvars in
                 if   n = 0
                 then abb.TEnv.type_abbrev_type
                 else let err =
                        TExc.PartialTypeConstructorApplication (tc, n, 0)
                      in raise (TExc.Error (loc, err)))
      | TE_tapp ({type_expr = TE_tname (m, t); _} as c, args) ->
          let tc = mk_full_tname m t in
          (match TEnv.lookup_type_abbrev env tc with
             | None ->
                 let args' = List.map expand args in
                 {te with type_expr = TE_tapp (c, args')}
             | Some abb ->
                 let n = List.length abb.TEnv.type_abbrev_tvars in
                 if   n != List.length args
                 then let err = TExc.PartialTypeConstructorApplication
                                  (tc, n, List.length args) in
                      raise (TExc.Error (loc, err))
                 else let args' = List.map expand args in
                      let map = List.combine abb.TEnv.type_abbrev_tvars args' in
                      subst map abb.TEnv.type_abbrev_type)

      | TE_tapp (c, args) ->
          let c' = expand c in
          let args' = List.map expand args in
          {te with type_expr = TE_tapp (c', args')}

  and subst map te =
    match te.type_expr with
      | TE_tvar _ ->
          te
      (* only apply the subst to local (inferred) type identifiers *)
      | TE_tname (Modul (Mod_inferred _), t) ->
          let s = Location.value t in
          (match List.assoc_opt (TName s) map with
             | None    -> te
             | Some te -> te)
      | TE_tname _ ->
          te
      | TE_tapp (c, args) ->
          let c' = subst map c in
          let args' = List.map (subst map) args in
          {te with type_expr = TE_tapp (c', args')}

  in expand te

let lookup_bitfield_info tenv m t =
  let l  = Location.loc t in
  let tt = mk_full_tname m t in
  let adt = match TEnv.lookup_adt tenv tt with
      | None     -> let err = TExc.UnboundRecord tt in
                    raise (TExc.Error (l, err))
      | Some adt -> adt in
  match adt with
    | {adt = Variant _; _} ->
        let err = TExc.NotRecordType t in
        raise (TExc.Error (Location.loc t, err))
    | {adt = Record {bitfield_info = None; _}; _} ->
        let err = TExc.NotBitfieldType t in
        raise (TExc.Error (Location.loc t, err))
    | {adt = Record {bitfield_info = Some bfi; _}; _} ->
        bfi

let lookup_bitfield_length tenv m t =
  let bfi = lookup_bitfield_info tenv m t in
  bfi.bf_length

let lookup_bitfield_fields tenv m t =
  let bfi = lookup_bitfield_info tenv m t in
  bfi.bf_fields

(* A helper to check if a bound for the repeat combinator is
 * non-zero. It uses a primitive constant-folder that does not access
 * the environment; a better approach would be to have an actual
 * const-folding pass before this analysis.
 *
 * NOTE: The below const-folder strips type annotations for
 * simplicity, and so the result cannot be used to replace the source
 * argument. *)

let rec const_fold: 't 'v 'm. ('t, 'v, 'm) expr -> ('t, 'v, 'm) expr =
  fun e ->
  match e.expr with
    | E_var _ | E_literal _ | E_mod_member _ | E_apply _ | E_constr _ ->
        e
    | E_match _ | E_record _ | E_field _ | E_let _ | E_case _ ->
        (* Although these could be reduced in theory, it is unlikely
         * to be useful in this context. *)
        e
    | E_cast (e, _) ->
        (* This loses information, but that's ok as long as we don't
         * replace the source with the result. *)
        const_fold e
    | E_unop (op, e') ->
        let e' = const_fold e' in
        (match op, e'.expr with
           | Uminus _, E_literal (PL_int (i, n)) ->
               let i = -i in
               (if   not (AstUtils.check_int_literal n i)
                then let err = TExc.Invalid_integer_value (i, n) in
                     raise (TExc.Error (e.expr_loc, err)));
               {e with expr = E_literal (PL_int (-i, n))}
           | Inot _, E_literal (PL_int (i, n)) ->
               let i = Int.lognot i in
               (if   not (AstUtils.check_int_literal n i)
                then let err = TExc.Invalid_integer_value (i, n) in
                     raise (TExc.Error (e.expr_loc, err)));
               {e with expr = E_literal (PL_int (-i, n))}
           | Not, E_literal (PL_bool b) ->
               {e with expr = E_literal (PL_bool (not b))}
           | _ ->
              {e with expr = E_unop (op, e')})
    | E_binop (op, l, r) ->
        let l', r' = const_fold l, const_fold r in
        (match op, l'.expr, r'.expr with
           | Lt on, E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && ln = rn ->
               {e with expr = E_literal (PL_bool (l < r))}
           | Gt on,   E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && ln = rn ->
               {e with expr = E_literal (PL_bool (l > r))}
           | Lteq on, E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && ln = rn ->
               {e with expr = E_literal (PL_bool (l <= r))}
           | Gteq on, E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && ln = rn ->
               {e with expr = E_literal (PL_bool (l >= r))}
           | Plus on, E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && ln = rn ->
               let v = l + r in
               if   not (AstUtils.check_int_literal on v)
               then let err = TExc.Invalid_integer_literal (v, on) in
                    raise (TExc.Error (e.expr_loc, err))
               else {e with expr = E_literal (PL_int (v, on))}
           | Minus on, E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && ln = rn ->
               let v = l - r in
               if   not (AstUtils.check_int_literal on v)
               then let err = TExc.Invalid_integer_literal (v, on) in
                    raise (TExc.Error (e.expr_loc, err))
               else {e with expr = E_literal (PL_int (v, on))}
           | Mult on, E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && ln = rn ->
               let v = l * r in
               if   not (AstUtils.check_int_literal on v)
               then let err = TExc.Invalid_integer_literal (v, on) in
                    raise (TExc.Error (e.expr_loc, err))
               else {e with expr = E_literal (PL_int (v, on))}
           | Mod _,  E_literal (PL_int _), E_literal (PL_int (r, _))
                when r = 0 ->
               raise (TExc.Error (e.expr_loc, TExc.Possible_division_by_zero))
           | Mod on,  E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && ln = rn ->
               let v = l mod r in
               if   not (AstUtils.check_int_literal on v)
               then let err = TExc.Invalid_integer_literal (v, on) in
                    raise (TExc.Error (e.expr_loc, err))
               else {e with expr = E_literal (PL_int (v, on))}
           | Div _,  E_literal (PL_int _), E_literal (PL_int (r, _))
                when r = 0 ->
               raise (TExc.Error (e.expr_loc, TExc.Possible_division_by_zero))
           | Div on,  E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && ln = rn ->
               let v = l / r in
               if   not (AstUtils.check_int_literal on v)
               then let err = TExc.Invalid_integer_literal (v, on) in
                    raise (TExc.Error (e.expr_loc, err))
               else {e with expr = E_literal (PL_int (v, on))}
           | Iand on, E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && ln = rn ->
               let v = Int.logand l r in
               if   not (AstUtils.check_int_literal on v)
               then let err = TExc.Invalid_integer_literal (v, on) in
                    raise (TExc.Error (e.expr_loc, err))
               else {e with expr = E_literal (PL_int (v, on))}
           | Ior on, E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && ln = rn ->
               let v = Int.logor l r in
               if   not (AstUtils.check_int_literal on v)
               then let err = TExc.Invalid_integer_literal (v, on) in
                    raise (TExc.Error (e.expr_loc, err))
               else {e with expr = E_literal (PL_int (v, on))}
           | Ixor on, E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && ln = rn ->
               let v = Int.logxor l r in
               if   not (AstUtils.check_int_literal on v)
               then let err = TExc.Invalid_integer_literal (v, on) in
                    raise (TExc.Error (e.expr_loc, err))
               else {e with expr = E_literal (PL_int (v, on))}
           | Lshft on, E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && rn = Ast.u8_t ->
               let v = Int.shift_left l r in
               if   not (AstUtils.check_int_literal on v)
               then let err = TExc.Invalid_integer_literal (v, on) in
                    raise (TExc.Error (e.expr_loc, err))
               else {e with expr = E_literal (PL_int (v, on))}
           | Rshft on, E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && rn = Ast.u8_t ->
               let v = Int.shift_right_logical l r in
               if   not (AstUtils.check_int_literal on v)
               then let err = TExc.Invalid_integer_literal (v, on) in
                    raise (TExc.Error (e.expr_loc, err))
               else {e with expr = E_literal (PL_int (v, on))}
           | Ashft on, E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when on = ln && rn = Ast.u8_t ->
               let v = Int.shift_right l r in
               if   not (AstUtils.check_int_literal on v)
               then let err = TExc.Invalid_integer_literal (v, on) in
                    raise (TExc.Error (e.expr_loc, err))
               else {e with expr = E_literal (PL_int (v, on))}
           | Land, E_literal (PL_bool l), E_literal (PL_bool r) ->
               {e with expr = E_literal (PL_bool (l && r))}
           | Lor,  E_literal (PL_bool l), E_literal (PL_bool r) ->
               {e with expr = E_literal (PL_bool (l || r))}
           (* Eq and Neq are polymorphic. *)
           | Eq,   E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when ln = rn ->
               {e with expr = E_literal (PL_bool (l = r))}
           | Eq,   E_literal (PL_bytes l), E_literal (PL_bytes r) ->
               {e with expr = E_literal (PL_bool (l = r))}
           | Eq,   E_literal PL_unit, E_literal PL_unit ->
               {e with expr = E_literal (PL_bool true)}
           | Eq,   E_literal (PL_bool l), E_literal (PL_bool r) ->
               {e with expr = E_literal (PL_bool (l = r))}
           | Eq,   E_literal (PL_bit l), E_literal (PL_bit r) ->
               {e with expr = E_literal (PL_bool (l = r))}
           | Eq,   E_literal (PL_bitvector l), E_literal (PL_bitvector r) ->
               {e with expr = E_literal (PL_bool (l = r))}
           | Neq,  E_literal (PL_int (l, ln)), E_literal (PL_int (r, rn))
                when ln = rn ->
               {e with expr = E_literal (PL_bool (not (l = r)))}
           | Neq,  E_literal (PL_bytes l), E_literal (PL_bytes r) ->
               {e with expr = E_literal (PL_bool (not (l = r)))}
           | Neq,  E_literal PL_unit, E_literal PL_unit ->
               {e with expr = E_literal (PL_bool false)}
           | Neq,  E_literal (PL_bool l), E_literal (PL_bool r) ->
               {e with expr = E_literal (PL_bool (not (l = r)))}
           | Neq,  E_literal (PL_bit l), E_literal (PL_bit r) ->
               {e with expr = E_literal (PL_bool (not (l = r)))}
           | Neq,  E_literal (PL_bitvector l), E_literal (PL_bitvector r) ->
               {e with expr = E_literal (PL_bool (not (l = r)))}
           | _ ->
               {e with expr = E_binop (op, l', r')})
    | E_recop ((m, t, rop), e') ->
        {e with expr = E_recop ((m, t, rop), const_fold e')}
    | E_bitrange (e', n, m) ->
        {e with expr = E_bitrange (const_fold e', n, m)}

let is_non_zero: 't 'v 'm. ('t, 'v, 'm) expr -> bool =
  fun e ->
  match (const_fold e).expr with
    | E_literal (PL_int (i, _)) -> i != 0
    | _                         -> true


(* Extract a nested sequence of field accessors in an expression,
   along with the head variable.  This is usually applied to check
   whether an expression is a reference. *)
let lhs_fields (type b m) e : ((string * b) * (m modul * string) list) option =
  let rec traverse (acc: (m modul * string) list) e =
    match e.expr with
      | E_field (e', (m, f)) ->
          traverse ((m, Location.value f) :: acc) e'
      | E_var v ->
          Some (Location.value v, acc)
      | _ ->
          None in
  traverse [] e

(* Guesses whether the rule element `rle` is composed of only regexps,
   such that it can be condensed into a single regexp.
   Since no environment is provided, it assumes any non-terminals are
   not regular expressions.  This is more lenient than
   `is_regexp_elem` since it allows constraints.  It is typically
   called for the rules of a regexp-nonterminal.

   Since scans are not handled as regular expressions, treat them as
   non-regexp rule elements.
 *)
let rec guess_is_regexp_elem rle =
  match rle.rule_elem with
    | RE_epsilon
    | RE_regexp _ -> true

    | RE_opt rle'
    | RE_star (rle', None) -> guess_is_regexp_elem rle'

    | RE_star (rle', Some e) ->
        (match (const_fold e).expr with
           | E_literal (PL_int _) -> guess_is_regexp_elem rle'
           | _                    -> false)

    | RE_choice rles
    | RE_seq rles
    | RE_seq_flat rles -> List.for_all guess_is_regexp_elem rles

    | RE_constraint _
    | RE_suspend_resume _
    | RE_named _
    | RE_action _
    | RE_non_term _
    | RE_bitvector _
    | RE_bitfield _
    | RE_align _
    | RE_pad _
    | RE_scan _
    | RE_at_pos _
    | RE_at_view _
    | RE_set_view _
    | RE_map_views _ -> false

(* Checks whether the rule element `rle` is composed of only regexps,
   such that it can be condensed into a single regexp.
   Since an environment is provided, it looks up the types of any
   non-terminals to check whether they are regular expressions. *)
let rec is_regexp_elem tenv modul rle =
  match rle.rule_elem with
    | RE_epsilon
    | RE_regexp _ -> true

    | RE_opt rle'
    | RE_star (rle', None) -> is_regexp_elem tenv modul rle'

    | RE_star (rle', Some e) ->
        (match (const_fold e).expr with
           | E_literal (PL_int _) -> is_regexp_elem tenv modul rle'
           | _                    -> false)

    | RE_choice rles
    | RE_seq rles
    | RE_seq_flat rles -> List.for_all (is_regexp_elem tenv modul) rles

    (* We currently do not support cross-module non-stdlib regexps
       since the DFAs are inlined during construction. *)
    | RE_non_term (m, _, _)
         when m <> AstUtils.stdlib && AstUtils.mod_compare m modul != 0 ->
        false
    (* TODO: we currently don't support attributed regexp
       non-terminals. But they should be possible to support as long
       as the attributes can be constant folded, and there is a
       statically known regexp expansion for each of the constant
       attribute combinations used in the spec. *)
    | RE_non_term (m, nid, None) ->
        let n = Location.value nid in
        (match TEnv.lookup_non_term_type tenv (m, (NName n)) with
           | Some t -> TypeAlgebra.is_regexp_type (TEnv.typcon_variable tenv) t
           | None   -> false)

    | RE_non_term _
    | RE_named _
    | RE_action _
    | RE_constraint _
    | RE_suspend_resume _
    | RE_bitvector _
    | RE_bitfield _
    | RE_align _
    | RE_pad _
    | RE_scan _
    | RE_at_pos _
    | RE_at_view _
    | RE_set_view _
    | RE_map_views _ -> false

let is_regexp_rule tenv modul r =
     List.length r.rule_temps = 0
  && List.for_all (is_regexp_elem tenv modul) r.rule_rhs

(* Converts a typed regexp rule element into a regexp.  It maintains
   the aux and location information as best it can.  It assumes that
   `r` satisfies `is_regexp_elem r`.
 *)
let rec rule_elem_to_regexp r =
  let wrap r' = {regexp = r';
                 regexp_mod = r.rule_elem_mod;
                 regexp_loc = r.rule_elem_loc;
                 regexp_aux = r.rule_elem_aux} in
  match r.rule_elem with
    | RE_epsilon ->
        wrap RX_empty
    | RE_regexp r' ->
        r'
    | RE_non_term (m, nid, None) ->
        wrap (RX_type (m, nid))

    | RE_star (r', None) ->
        wrap (RX_star (rule_elem_to_regexp r', None))
    | RE_star (r', Some e) ->
        let e' = const_fold e in
        (match e'.expr with
           | E_literal (PL_int _) -> ()
           | _                    -> assert false);
        wrap (RX_star (rule_elem_to_regexp r', Some e'))

    | RE_opt r' ->
        wrap (RX_opt (rule_elem_to_regexp r'))
    | RE_choice rs ->
        let rs' = List.map rule_elem_to_regexp rs in
        wrap (RX_choice rs')
    | RE_seq rs | RE_seq_flat rs ->
        let rs' = List.map rule_elem_to_regexp rs in
        wrap (RX_seq rs')
    | _ ->
        assert false

(* Converts a typed rule into a regexp.  It maintains the aux and
   location information as best it can.  It assumes that `r` satisfies
   `is_regexp_rule r`. *)
let rule_to_regexp m r =
  assert (List.length r.rule_temps = 0);
  assert (List.length r.rule_rhs > 0);
  (* Since all regexps have the same type, we use the type from the
     first element. *)
  let rx = List.hd r.rule_rhs in
  let rxs = List.map rule_elem_to_regexp r.rule_rhs in
  {regexp     = RX_seq rxs;
   regexp_mod = m;
   regexp_loc = r.rule_loc;
   regexp_aux = rx.rule_elem_aux}

(* Converts a sequence of typed rules into a regexp.  It maintains the
   aux and location information as best it can.  It assumes that each
   rule `r` in `rs` satisfies `is_regexp_rule r`. *)
let rules_to_regexp m rs =
  let rxs = List.map (rule_to_regexp m) rs in
  let rxh = List.hd rxs in
  let rxt = List.hd (List.rev rxs) in
  {regexp     = RX_choice rxs;
   regexp_loc = Location.extent rxh.regexp_loc rxt.regexp_loc;
   regexp_mod = m;
   regexp_aux = rxh.regexp_aux}

(* Separate out the trailing fields for a nested record expression. *)
let fields_suffix e =
  let rec split e fs =
    match e.expr with
      | E_field (e', f) -> split e' (f :: fs)
      | _               -> e, fs in
  split e []

(* utilities to make ast types comparable by syntactical equality, by
   normalizing location and aux information *)

let unwrap_id id =
  Location.mk_loc_val (Location.value id) Location.ghost_loc

let unwrap_mod m =
  match m with
    | Modul (Mod_explicit m) -> Modul (Mod_explicit (unwrap_id m))
    | m                      -> m

let unwrap_var v =
  Location.mk_loc_val (var_name v, ()) Location.ghost_loc

let unwrap_constructor (m, typ, constr) =
  (unwrap_mod m, unwrap_id typ, unwrap_id constr)

let rec unwrap_typ typ =
  let t = match typ.type_expr with
      | TE_tvar t ->
          TE_tvar (unwrap_id t)
      | TE_tname (m, t) ->
          TE_tname (unwrap_mod m, unwrap_id t)
      | TE_tapp (c, ts) ->
          TE_tapp (unwrap_typ c, List.map unwrap_typ ts) in
  {type_expr = t; type_expr_loc = Location.ghost_loc}

let rec unwrap_pat pat =
  let p = match pat.pattern with
      | P_wildcard ->
          P_wildcard
      | P_var v ->
          P_var (unwrap_var v)
      | P_literal l ->
          P_literal l
      | P_variant (c, ps) ->
          P_variant (unwrap_constructor c, List.map unwrap_pat ps) in
  {pattern = p; pattern_loc = Location.ghost_loc; pattern_aux = ()}

let rec unwrap_exp exp =
  let e = match exp.expr with
      | E_var v ->
          E_var (unwrap_var v)
      | E_constr (c, es) ->
          let c = unwrap_constructor c in
          E_constr (c, List.map unwrap_exp es)
      | E_record fs ->
          E_record (List.map
                      (fun ((m, f), e) ->
                        ((m, unwrap_id f), unwrap_exp e)
                      ) fs)
      | E_apply (f, es) ->
          E_apply (unwrap_exp f, List.map unwrap_exp es)
      | E_unop (op, e) ->
          E_unop (op, unwrap_exp e)
      | E_binop (op, l, r) ->
          E_binop (op, unwrap_exp l, unwrap_exp r)
      | E_recop ((m, r, rop), e) ->
          E_recop ((unwrap_mod m, unwrap_id r, unwrap_id rop), unwrap_exp e)
      | E_bitrange (e, n, m) ->
          E_bitrange (unwrap_exp e, n, m)
      | E_match (e, (m, t, c)) ->
          E_match (unwrap_exp e, (unwrap_mod m, unwrap_id t, unwrap_id c))
      | E_literal l ->
          E_literal l
      | E_field (e, (m, f)) ->
          E_field (unwrap_exp e, (m, unwrap_id f))
      | E_mod_member (m, v) ->
          E_mod_member (unwrap_id m, unwrap_id v)
      | E_let (p, e, b) ->
          E_let (unwrap_pat p, unwrap_exp e, unwrap_exp b)
      | E_case (e, bs) ->
          let bs' =
            List.map (fun (p, e') -> unwrap_pat p, unwrap_exp e') bs in
          E_case (unwrap_exp e, bs')
      | E_cast (e, t) ->
          E_cast (unwrap_exp e, unwrap_typ t) in
  {expr = e; expr_loc = Location.ghost_loc; expr_aux = ()}
