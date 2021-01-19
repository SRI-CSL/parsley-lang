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

(** This module implements type inference and checking. *)

open Misc
open TypeConstraint
open TypeAlgebra
open MultiEquation
open TypingEnvironment
open TypingExceptions
open Ast

(** {2 Inference} *)

(** A fragment denotes the typing information acquired in a match branch.
    [gamma] is the typing environment coming from the binding of pattern
    variables. [vars] are the fresh variables introduced to type the
    pattern. [tconstraint] is the constraint coming from the instantiation
    of the data constructor scheme. *)
type fragment =
  {gamma       : (crterm * Location.t) StringMap.t;
   vars        : variable list;
   tconstraint : tconstraint}

(** The [empty_fragment] is used when nothing has been bound. *)
let empty_fragment =
  {gamma       = StringMap.empty;
   vars        = [];
   tconstraint = CTrue Location.ghost_loc}

(** Joining two fragments is straightforward except that the environments
    must be disjoint (a pattern cannot bound a variable several times). *)
let join_fragment pos f1 f2 =
  {gamma =
     (try
        StringMap.strict_union f1.gamma f2.gamma
      with StringMap.Strict x -> raise (Error (NonLinearPattern (pos, x))));
   vars        = f1.vars @ f2.vars;
   tconstraint = f1.tconstraint ^ f2.tconstraint}

(** [infer_pat_fragment p t] generates a fragment that represents the
    information gained by a success when matching p. *)
let infer_pat_fragment tenv (p: unit pattern) (t: crterm) : fragment * crterm pattern =
  let join pos = List.fold_left (join_fragment pos) empty_fragment in
  let mk_auxpat p' =
    {pattern = p'; pattern_loc = p.pattern_loc; pattern_aux = t} in
  let rec infpat t p =
    let pos = p.pattern_loc in
    match p.pattern with
      (* Wildcard pattern does not generate any fragment. *)
      | P_wildcard ->
          empty_fragment, mk_auxpat P_wildcard

      (* We refer to the algebra to know the type of a primitive. *)
      | P_literal l ->
          {empty_fragment with
            tconstraint = (t =?= type_of_primitive (as_fun tenv) l) pos},
          mk_auxpat (P_literal l)

      (* Matching against a variable generates a fresh flexible
         variable, binds it to the [name] and forces the variable to
         be equal to [t]. *)
      | P_var name ->
          let pos = Location.loc name in
          let v = variable Flexible () in
          {gamma       = StringMap.singleton
                           (Location.value name)
                           (CoreAlgebra.TVariable v, pos);
           tconstraint = (CoreAlgebra.TVariable v =?= t) pos;
           vars        = [ v ]},
          mk_auxpat (P_var name)

      (* Matching against a data constructor generates the fragment
         that:
         - forces [t] to be the type of the constructed value
         - constraints the types of the subpatterns to be equal to the
           arguments of the data constructor. *)
      | P_variant ((typ, c), ps) ->
          let typid = Location.value typ in
          let cid, cloc = Location.value c, Location.loc c in
          let dcid = TypeConv.canonicalize_dcon typid cid in
          let alphas, ct = fresh_datacon_scheme tenv cloc (DName dcid) in
          let rt = result_type (as_fun tenv) ct
          and ats = arg_types (as_fun tenv) ct in
          if List.length ps <> List.length ats then
            let err =
              InvalidPatternArgs (pos, c, List.length ats, List.length ps) in
            raise (Error (err))
          else
            let fps = List.map2 infpat ats ps in
            let fs, ps' = List.split fps in
            let fragment = join pos fs in
            {fragment with
              tconstraint = fragment.tconstraint ^ (t =?= rt) pos;
              vars        = alphas @ fragment.vars},
            mk_auxpat (P_variant ((typ, c), ps'))
  (* TODO: add record patterns *) in
  infpat t p

(** checks for consistency between the declarations and
    uses of type variables *)
let check_distinct_tvars _typid qs =
  let rec checker acc = function
    | [] -> None
    | var :: tl ->
        let v = Location.value var in
        if StringSet.mem v acc
        then Some var
        else checker (StringSet.add v acc) tl in
  match checker StringSet.empty qs with
    | Some var -> raise (Error (DuplicateTypeVariable var))
    | None -> ()

let check_tvars_usage tenv _t qs used_set =
  (* TODO: ensure tycons don't cause issues; perhaps only extract
     syntactic type-variables to avoid tycons *)
  (* make sure all declared type variables are used *)
  let decl_vs =
    List.fold_left (fun acc q ->
        let v = Location.value q in
        if not (StringMap.mem v used_set)
        then raise (Error (UnusedTypeVariable q))
        else StringSet.add v acc
      ) StringSet.empty qs in
  (* make sure all used vars are declared or defined *)
  StringMap.iter (fun v loc ->
      if not (StringSet.mem v decl_vs
              || is_defined_type tenv (TName v))
      then
        raise (Error (UnboundTypeIdentifier (loc, (TName v))))
    ) used_set

(** [make_dc_signature adt tvars dc typ] constructs the function type
    signature for a data constructor of [adt] named [dc] given its declared
    argument [typ], which is parameterized over type variables [tvars]. *)
let make_dc_signature adt tvars _dc typ =
  let tvars = List.map AstUtils.make_tvar_ident tvars in
  let res =
    if List.length tvars = 0
    then AstUtils.make_tvar_ident adt
    else AstUtils.make_type_app_name (Location.value adt) tvars
           (Location.loc adt) in
  match typ with
    | None -> res
    | Some sign -> AstUtils.add_arrow_result sign res

(** [intern_data_constructor external adt_ident env_info dcon_info] returns
    env_info augmented with the data constructor's typing information
    It also checks if its definition is legal. [internal] specifies
    whether this is a builtin or from an external spec.
*)
let intern_data_constructor internal adt_id qs env_info dcon_info =
  let adt_name = Location.value adt_id in
  let tenv, acu, lrqs, let_env = env_info
  and dname, opt_arg = dcon_info in
  let typ =
    (* Internal builtins have full signatures, whereas parsed
       signatures leave the result type implicit.  This shows up in
       constant data constructors, where make_dc_signature would
       otherwise add an unnecessary return type. *)
    if internal then unSome opt_arg
    else make_dc_signature adt_id qs dname opt_arg in
  let qs = List.map (fun q -> TName (Location.value q)) qs in
  let rqs, rtenv = fresh_unnamed_rigid_vars (Location.loc adt_id) tenv qs in
  let tenv' = add_type_variables rtenv tenv in
  let ityp = TypeConv.intern tenv' typ in
  let _ =
    if not (is_regular_datacon_scheme tenv (TName adt_name) rqs ityp) then
      raise (Error (InvalidDataConstructorDefinition dname)) in
  let pos = Location.loc dname in
  let dname = Location.value dname in
  let binding = TypeConv.canonicalize_dcon adt_name dname in
  let v = variable ~structure:ityp Flexible () in
  ((add_data_constructor tenv pos (TName adt_name) (DName binding)
      (TypeConv.arity typ, rqs, ityp)),
   (DName dname, v) :: acu,
   (rqs @ lrqs),
   StringMap.add binding (ityp, pos) let_env)

(** [make_field_signature adt tvars f typ] constructs the field type
    and the function type signature for a destructor of [adt] named
    [f] given its declared argument [typ], which is parameterized over
    type variables [tvars]. *)
let make_field_signature adt tvars f typ =
  let tvars = List.map AstUtils.make_tvar_ident tvars in
  let source =
    if List.length tvars = 0
    then AstUtils.make_tvar_ident adt
    else AstUtils.make_type_app_name (Location.value adt) tvars
           (Location.loc adt) in
  (* TODO: we forbid function types as field types.  Currently, this
     is by enforced by construction at the syntax level, but we should
     also check it here, e.g. for builtins. *)
  AstUtils.make_arrow_type [source; typ] (Location.loc f)

(** [intern_field_destructor adt_name env_info f_info] returns
    env_info augmented with the field destructor's typing information
    It also checks if its definition is legal. *)
let intern_field_destructor adt_id qs env_info f_info =
  let adt_name = Location.value adt_id in
  let tenv, acu, lrqs, let_env = env_info
  and fname, typ = f_info in
  let destructor = make_field_signature adt_id qs fname typ in
  let qs = List.map (fun q -> TName (Location.value q)) qs in
  let rqs, rtenv = fresh_unnamed_rigid_vars (Location.loc adt_id) tenv qs in
  let tenv' = add_type_variables rtenv tenv in
  let ityp = TypeConv.intern tenv' destructor in
  let _ =
    if not (is_regular_field_scheme tenv (TName adt_name) rqs ityp) then
      raise (Error (InvalidFieldDestructorDefinition fname)) in
  let pos = Location.loc fname in
  let fname = Location.value fname in
  let binding = Printf.sprintf "{%s}" fname in
  let v = variable ~structure:ityp Flexible () in
  ((add_field_destructor tenv pos (TName adt_name) (LName fname)
      (rqs, ityp)),
   (LName fname, v) :: acu,
   (rqs @ lrqs),
   StringMap.add binding (ityp, pos) let_env)

(* The constructor is the function with argument types from the fields
   in increasing order, and with the record as the result type. *)
let make_record_signature adt tvars fields =
  let tvars = List.map AstUtils.make_tvar_ident tvars in
  let res =
    if List.length tvars = 0
    then AstUtils.make_tvar_ident adt
    else AstUtils.make_type_app_name (Location.value adt) tvars
           (Location.loc adt) in
  let fields = AstUtils.sort_fields fields in
  let signature =
    List.fold_left (fun acc (f, t) ->
        AstUtils.make_arrow_type [t; acc] (Location.loc f)
      ) res (List.rev fields) in
    signature, fields

(** [intern_record_constructor adt_name env_info fields] returns
    env_info augmented with the record constructor's typing
    information.  The constructor is named '<adt>' for a record named
    'adt'.
*)
let intern_record_constructor adt_id qs env_info fields =
  let adt_name = Location.value adt_id in
  let tenv, let_env = env_info in
  let rcon = Printf.sprintf "<%s>" adt_name in
  let constructor, _fields = make_record_signature adt_id qs fields in
  let qs = List.map (fun q -> TName (Location.value q)) qs in
  let rqs, rtenv = fresh_unnamed_rigid_vars (Location.loc adt_id) tenv qs in
  let tenv' = add_type_variables rtenv tenv in
  let ityp = TypeConv.intern tenv' constructor in
  let pos = Location.loc adt_id in
  let v = variable ~structure:ityp Flexible () in
  ((add_record_constructor tenv (TName adt_name) (rqs, ityp)),
   (TName rcon, v),
   rqs,
   StringMap.add rcon (ityp, pos) let_env)

(** [check_valid_type_defn t qs defn] checks whether [defn] is a valid type
    definition for the declared quantified type variables [qs]. *)
let check_valid_type_defn tenv t qs defn =
  check_tvars_usage tenv t qs (TypeConv.variables_of_typ defn)

(** Constraint contexts. *)
type context = tconstraint -> tconstraint

(** A set of possibly mutually recursive type definitions are
   processed as follows:

 . each type constructor and its kind in the set is registered in the
   environment without any [adt_info], but a set of references is
   collected which point to where their [adt_info] can be updated
   later.

 . the [type_rep] of each constructor is now processed in this
   environment, and the computed [adt_info] is registered using the
   reference for that constructor collected above.
*)

let rec infer_type_decls tenv ctxt tdsloc tds =
  let tenv', tdsrefs, vs =
    List.fold_left (fun (tenv, tdsrefs, vs) td ->
        let name  = Location.value td.type_decl_ident in
        let loc   = td.type_decl_loc in
        let kind  = td.type_decl_kind in
        let kenv  = as_kind_env tenv in
        let k     = KindInferencer.intern_kind kenv kind in
        let v     = variable ~name:(TName name) Constant () in
        let adt   = ref None in
        let tenv' =
          add_type_constructor tenv loc (TName name) (k, v, adt) in
        tenv', (td, adt) :: tdsrefs, v :: vs
      ) (tenv, [], []) tds in
  (* These types and their constructors/destructors need to be placed
     in the same let binding set, so collect all the variables and
     bindings involved before creating the context. *)
  let tenv, rqs, let_env =
    List.fold_left (fun (tenv, rqs, let_env) (td, adt_ref) ->
        infer_type_decl (tenv, rqs, let_env) td adt_ref
      ) (tenv', [], StringMap.empty) tdsrefs in
  (* Now construct the new constraint context.*)
  let ctxt =
    (fun c ->
      ctxt (
          (* Universally quantify the type constructor variables in an
             outer context.*)
          fl ~pos:tdsloc vs
            (* Construct the let binding environment for the
               data constructors and destructors. *)
            (CLet ([Scheme (tdsloc, rqs, [],
                            CTrue tdsloc,
                            let_env)],
                   (* Place the input constraint under these bindings.*)
                   c))
    )) in
  tenv, ctxt

(* Perform the second step of type declaration processing: the body of
   each type declaration is processed and added to the environment
   created in the first step.  This step collects the variables and
   bindings needed for the final constraint context for the recursive
   definitions.
*)
and infer_type_decl (tenv, rqs, let_env) td adt_ref =
  let ident = td.type_decl_ident
  and loc   = td.type_decl_loc
  and tvars = td.type_decl_tvars
  and typ   = td.type_decl_body in
  check_distinct_tvars ident tvars;
  match typ.type_rep with
    | TR_variant dcons ->
        (* First expand any type abbreviations in the signatures *)
        let dcons =
          List.map (function
              | d, None ->
                  d, None
              | d, Some te ->
                  d, Some (AstUtils.expand_type_abbrevs tenv te)
            ) dcons in
        (* Add the constructor signatures to the environment *)
        let tenv, ids, rqs, let_env =
          List.fold_left
            (* [false] indicates this is user-specified *)
            (intern_data_constructor false ident tvars)
            (tenv, [], rqs, let_env)
            dcons in
        (* Fill in the adt_info *)
        adt_ref := Some {adt = Variant ids; loc};
        tenv, rqs, let_env
    | TR_record fields ->
        (* First expand any type abbreviations in the signatures *)
        let fields =
          List.map (fun (f, te) ->
              f, AstUtils.expand_type_abbrevs tenv te
            ) fields in
        (* Add the record and field signatures into the environment *)
        let tenv, dids, drqs, let_env =
          List.fold_left
            (intern_field_destructor ident tvars)
            (tenv, [], rqs, let_env)
            fields in
        let tenv, cid, crqs, let_env =
          intern_record_constructor ident tvars
            (tenv, let_env) fields in
        let fields, _ = List.split fields in
        (* Fill in the adt_info *)
        adt_ref := Some {adt = Record {adt = ident;
                                       fields;
                                       record_constructor = cid;
                                       field_destructors = dids};
                          loc};
        tenv, crqs @ drqs, let_env
    | TR_defn _ ->
        (* This is prevented by the check for type abbreviations in
           infer_spec. *)
        assert false

(* Type abbreviations are just registered in the environment and are
   fully expanded whereever they are used, and so they do not modify
   or appear in constraint contexts.  This allows polymorphic
   abbreviations (which otherwise cannot be supported in this HMX
   engine), at the expense of larger constraints and suboptimal
   error messages. *)
let infer_type_abbrev tenv td =
  let ident = td.type_decl_ident
  and tvars = td.type_decl_tvars
  and pos   = td.type_decl_loc
  and typ   = td.type_decl_body in
  let name  = Location.value ident in
  match typ.type_rep with
    | TR_defn d ->
        (* First expand any type abbreviations in this abbreviation *)
        let d' = AstUtils.expand_type_abbrevs tenv d in
        (* Check validity of the resulting type expression *)
        check_valid_type_defn tenv ident tvars d';
        (* Add it to the environment *)
        let tvs =
          List.map (fun tv -> TName (Location.value tv)) tvars in
        let abb = {type_abbrev_tvars = tvs;
                   type_abbrev_type = d'} in
        add_type_abbrev tenv pos (TName name) abb
    (* non-abbreviations are handled seperately via checks in infer_spec. *)
    | _ ->
        assert false

let make_match_case_expr exp typ dcon arity loc =
  let wc = AstUtils.make_pattern_loc P_wildcard loc in
  let mk_var s =
    let v = E_var (Location.mk_loc_val s loc) in
    AstUtils.make_expr_loc v loc in
  let rec mk_pats pats cnt =
    if cnt = 0 then pats else mk_pats (wc::pats) (cnt - 1) in
  let pargs = mk_pats [] arity in
  let pattern = AstUtils.make_pattern_loc (P_variant ((typ, dcon), pargs)) loc in
  let tr, fl = mk_var "bool::True", mk_var "bool::False" in
  let case_exp = E_case (exp, [pattern, tr; wc, fl]) in
  {expr = case_exp; expr_loc = loc; expr_aux = ()}

(** looks up the adt in [tenv] matching the [fields] in a literal
    record expression; it reports mismatch errors at location [loc]. *)
let lookup_record_adt tenv fields =
  let f = List.hd fields in (* nonempty list is ensured in the parser *)
  let fid = Location.value f in
  let adtid = match lookup_field_adt tenv (LName fid) with
      | Some adtid -> adtid
      | None -> raise (Error (UnboundRecordField (Location.loc f, LName fid))) in
  let rec_info, rec_loc = match lookup_adt tenv adtid with
      | Some {adt = Record rec_info; loc = rec_loc} ->
          rec_info, rec_loc
      | Some {adt = Variant _; _} ->
          (* Fields (initial lowercase) and data constructors (initial
             upppercase) cannot collide. *)
          assert false
      | None ->
          (* lookup_field_adt should have mapped the field name to a valid ADT. *)
          assert false in
  let adt_ident = let TName id = adtid in
                  Location.mk_loc_val id rec_loc in
  (* Make sure the used fields match the declared fields. *)
  let decset = List.fold_left (fun acc field ->
                   let l = Location.value field in
                   (* there should be no duplicates *)
                   assert (not (StringSet.mem l acc));
                   StringSet.add l acc
                 ) StringSet.empty rec_info.fields in
  let useset = List.fold_left (fun acc locid ->
                   let id = Location.value locid in
                   if StringSet.mem id acc then
                     raise (Error (RepeatedRecordField locid))
                   else if not (StringSet.mem id decset) then
                     raise (Error (InvalidRecordField (locid, adt_ident)))
                   else
                     StringSet.add id acc
                 ) StringSet.empty fields in
  (match StringSet.choose_opt (StringSet.diff decset useset) with
     | Some f -> raise (Error (IncompleteRecord (adt_ident, f)))
     | None -> ());
  rec_info

(** [infer_expr tenv e t] generates a constraint that guarantees that
    [e] has type [t] in the typing environment [tenv]. *)
let rec infer_expr tenv (e: unit expr) (t : crterm)
        : tconstraint * crterm expr =
  let mk_auxexpr e' =
    {expr = e'; expr_loc = e.expr_loc; expr_aux = t} in
  match e.expr with
    | E_var id ->
        (* The type of a variable must be at least as general as [t]. *)
        (SName (Location.value id) <? t) (Location.loc id),
        mk_auxexpr (E_var id)
    | E_constr ((adt, dcon), args) ->
        (* A data constructor application is similar to the usual
           application except that it must be fully applied. *)
        let typid = Location.value adt in
        let cid, cloc = Location.value dcon, Location.loc dcon in
        let dcid = TypeConv.canonicalize_dcon typid cid in
        let arity, _, _ = lookup_datacon tenv cloc (DName dcid) in
        let nargs = List.length args in
        if nargs <> arity then
          raise (Error (PartialDataConstructorApplication (dcon, arity, nargs)))
        else
          exists_list_aux args (
              fun exs ->
              let typ, c, args' =
                List.fold_left
                  (fun (typ, c, args') (arg, exvar) ->
                    let c', arg' = infer_expr tenv arg exvar in
                    TypeConv.arrow tenv exvar typ, c ^ c', arg' :: args')
                  (t, CTrue e.expr_loc, [])
                  (List.rev exs) in
              c ^ (SName dcid <? typ) e.expr_loc,
              mk_auxexpr (E_constr ((adt, dcon), args'))
            )

    | E_record fields ->
        (* Lookup the record ADT matched by this set of fields, and
           constrain each field value to the result type of the
           corresponding field destructor. *)
        let fields = AstUtils.sort_fields fields in
        let f_names, _ = List.split fields in
        let rec_info = lookup_record_adt tenv f_names in
        let rcon =
          Printf.sprintf "<%s>" (Location.value rec_info.adt) in
        exists_list_aux fields (
            fun exs ->
            let typ, c, fields' =
              List.fold_left
                (fun (typ, c, fields') ((fn, fv), exvar) ->
                  let c', fv' = infer_expr tenv fv exvar in
                  TypeConv.arrow tenv exvar typ, c ^ c', (fn, fv') :: fields')
                (t, CTrue e.expr_loc, [])
                (List.rev exs) in
            c ^ (SName rcon <? typ) e.expr_loc,
            (* annotated ast has fields in canonical order *)
            mk_auxexpr (E_record fields')
          )
    | E_field (exp, f) ->
        (* A record field index is similar to a data constructor but
           has no arity check; its constraint makes its destructor
           type equal to the type taking [exp] to [t].*)
        let field = Location.value f in
        let _ = lookup_field_destructor tenv (Location.loc f) (LName field) in
        let binding = Printf.sprintf "{%s}" field in
        exists_aux (fun exvar ->
            let c', exp' = infer_expr tenv exp exvar in
            let typ = TypeConv.arrow tenv exvar t in
            c' ^ (SName binding <? typ) e.expr_loc,
            mk_auxexpr (E_field (exp', f))
          )
    | E_apply (fexp, args) ->
        (* The constraint of an [apply] makes equal the type of the
           function expression [fexp] and the function type taking the
           types of arguments [args] to [t]. *)

        (* an empty argument list corresponds to an argument of unit *)
        if List.length args = 0 then
          let unit = typcon_variable tenv (TName "unit") in
          let typ = TypeConv.arrow tenv unit t in
          infer_expr tenv fexp typ
        else
          exists_list_aux args (
              fun exs ->
              let typ, cargs, args' =
                List.fold_left
                  (fun (typ, c, args') (arg, exvar) ->
                    let c', arg' = infer_expr tenv arg exvar in
                    TypeConv.arrow tenv exvar typ, c ^ c', arg' :: args')
                  (t, CTrue e.expr_loc, [])
                  (List.rev exs) in
              let cfun, fexp' = infer_expr tenv fexp typ in
              cfun ^ cargs,
              mk_auxexpr (E_apply (fexp', args'))
            )
    | E_match (exp, (typ, c)) ->
        (* Desugar this as a case expression:

           case (exp) {typ::c _ _ _ => true, _ => false}

           We cannot do it in the parser since we need to know the
           arity of the data constructor [typ::c] to generate the correct
           wildcard case pattern.  The return type is constrained to
           be boolean. *)
        let cid, cloc = Location.value c, Location.loc c in
        let dcid = TypeConv.canonicalize_dcon (Location.value typ) cid in
        let arity, _, _ = lookup_datacon tenv cloc (DName dcid) in
        let case_exp = make_match_case_expr exp typ c arity e.expr_loc in
        let bool_typ = type_of_primitive (as_fun tenv) (PL_bool true) in
        let c, exp' = infer_expr tenv case_exp t in
        c ^ (t =?= bool_typ) e.expr_loc,
        exp'  (* annotated ast has desugared form *)
    | E_literal prim_lit ->
        (* TODO: support various integer types *)
        let primtyp = type_of_primitive (as_fun tenv) prim_lit in
        (t =?= primtyp) e.expr_loc,
        mk_auxexpr (E_literal prim_lit)
    | E_case (exp, clauses) ->
        (* The constraint of a [case] makes equal the type of the
           scrutinee and the type of every branch pattern. The body
           of each branch must be equal to [t]. *)
        (* TODO: exhaustiveness check of patterns *)
        exists_aux (fun exvar ->
            let ce, exp' = infer_expr tenv exp exvar in
            let clauses' =
              List.map
                (fun (p, b) ->
                  let fragment, p' = infer_pat_fragment tenv p exvar in
                  let cb, b' = infer_expr tenv b t in
                  CLet ([ Scheme (p.pattern_loc, [], fragment.vars,
                                  fragment.tconstraint,
                                  fragment.gamma) ],
                        cb),
                  (p', b'))
                clauses in
            let ccl, clauses' = List.split clauses' in
            ce ^ conj ccl,
            mk_auxexpr (E_case (exp', clauses'))
          )
    | E_let (p, def, body) ->
        (* The constraint of this non-generalizing [let] makes equal
           the type of the pattern and the definiens, and requires
           the type of the let body to be equal to [t]. *)
        exists_aux (fun exvar ->
            let fragment, p' = infer_pat_fragment tenv p exvar in
            let cdef, def' = infer_expr tenv def exvar in
            (* Require [t] to be a valid type for [body]. *)
            let cbody, body' = infer_expr tenv body t in
            cdef
            ^ CLet ([ Scheme (e.expr_loc, [], fragment.vars,
                              (* Require [exvar] to be a valid type
                                 for [p]. *)
                              fragment.tconstraint,
                              fragment.gamma) ],
                    cbody),
            mk_auxexpr (E_let (p', def', body'))
          )
    | E_cast (exp, typ) ->
        (* A type constraint inserts a type equality into the
           generated constraint. *)
        let typ  = AstUtils.expand_type_abbrevs tenv typ in
        let ityp = TypeConv.intern tenv typ in
        let c, exp' = infer_expr tenv exp ityp in
        (t =?= ityp) e.expr_loc ^ c,
        mk_auxexpr (E_cast (exp', typ))
    | E_unop (op, e) ->
        (* This is a special case of a constructor application. *)
        exists_aux (fun exvar ->
            let opid = unop_const_name op in
            let typ = TypeConv.arrow tenv exvar t in
            let c, e' = infer_expr tenv e exvar in
            c ^ (SName opid <? typ) e.expr_loc,
            mk_auxexpr (E_unop (op, e'))
          )
    | E_binop (op, le, re) ->
        exists_aux (fun lexvar ->
            exists_aux (fun rexvar ->
                let opid = binop_const_name op in
                let typ = TypeConv.arrow tenv lexvar
                            (TypeConv.arrow tenv rexvar t) in
                let cle, le' = infer_expr tenv le lexvar in
                let cre, re' = infer_expr tenv re rexvar in
                cle ^ cre ^ (SName opid <? typ) e.expr_loc,
                mk_auxexpr (E_binop (op, le', re'))
              )
          )
    | E_mod_member (m, i) ->
        let mid = Location.value m in
        let vid = Location.value i in
        let loc = Location.extent (Location.loc m) (Location.loc i) in
        let _ = lookup_mod_item loc tenv (MName mid) (DName vid) in
        (* Use the encoded name registered in the environment *)
        let id = Printf.sprintf "%s.%s" mid vid in
        (* This is typed as a regular identifier. *)
        (SName id <? t) loc,
        mk_auxexpr (E_mod_member (m, i))

(* [infer_fun_defn tenv ctxt fd] examines the function definition [fd]
   and constraint context [ctxt] in the type environment [tenv] and
   generates an updated constraint context for [ctxt] and a type
   signature for [fd]. *)
let infer_fun_defn tenv ctxt fd =
  let loc = Location.loc fd.fun_defn_ident
  and fdn = Location.value fd.fun_defn_ident
  and qs = fd.fun_defn_tvars in
  let qs = List.map (fun q -> TName (Location.value q)) qs in
  let rqs, rtenv = fresh_unnamed_rigid_vars fd.fun_defn_loc tenv qs in
  let tenv' = add_type_variables rtenv tenv in

  (* Introduce a type variable for the function signature. *)
  let fv = variable Flexible () in
  let ftyp = CoreAlgebra.TVariable fv in

  (* First construct the function signature and the argument bindings
     for the body.  Handle the arguments as a simple case of lambda
     patterns; this will allow us to extend this later to proper
     pattern matching if needed.*)
  let restyp = AstUtils.expand_type_abbrevs tenv fd.fun_defn_res_type in
  let irestyp = TypeConv.intern tenv' restyp in
  let _, argbinders, signature =
    if List.length fd.fun_defn_params = 0 then
      (* functions without args have a signature of unit -> result_type *)
      let unit = typcon_variable tenv (TName "unit") in
      let signature = TypeConv.arrow tenv unit irestyp in
      StringMap.empty, empty_fragment, signature
    else
      List.fold_left (fun (acu_ids, bindings, signature) (pid, typ) ->
          let pn, ploc = Location.value pid, Location.loc pid in
          let acu_ids =
            match StringMap.find_opt pn acu_ids with
              | Some repid ->
                  raise (Error (RepeatedFunctionParameter (pid, repid)))
              | None ->
                  StringMap.add pn pid acu_ids in
          let typ = AstUtils.expand_type_abbrevs tenv typ in
          let ityp = TypeConv.intern tenv' typ in
          let v = variable Flexible () in
          acu_ids,
          {gamma = StringMap.add pn (CoreAlgebra.TVariable v, ploc)
                      bindings.gamma;
            tconstraint = (CoreAlgebra.TVariable v =?= ityp) ploc
                          ^ bindings.tconstraint;
            vars = v :: bindings.vars},
          TypeConv.arrow tenv ityp signature
        ) (StringMap.empty, empty_fragment, irestyp) (List.rev fd.fun_defn_params) in

  (* for recursive functions, add the function name to the let context. *)
  let gamma = if fd.fun_defn_recursive
              then StringMap.add fdn (ftyp, loc) argbinders.gamma
              else argbinders.gamma in
  let arg_schm = Scheme (fd.fun_defn_loc, [], argbinders.vars,
                         argbinders.tconstraint,
                         gamma) in

  (* Generate the typing constraint for the body. *)
  let cbody, body' = infer_expr tenv' fd.fun_defn_body irestyp in

  (* Construct the constrained binding for the polymorphic function
     definition itself. *)
  let scheme =
    let def_c = CLet ([arg_schm],
                      (ftyp =?= signature) loc
                      ^ cbody) in
    let bind = StringMap.singleton fdn (ftyp, loc) in
    Scheme (fd.fun_defn_loc, rqs, [fv], def_c, bind) in

  (* Generate the constraint context. *)
  (fun c -> ctxt (CLet ([scheme], c))),
  (* The annotated function contains the function signature and the
   * annotated body *)
  {fun_defn_ident     = fd.fun_defn_ident;
   fun_defn_tvars     = fd.fun_defn_tvars;
   fun_defn_params    = fd.fun_defn_params;
   fun_defn_res_type  = fd.fun_defn_res_type;
   fun_defn_body      = body';
   fun_defn_recursive = fd.fun_defn_recursive;
   fun_defn_loc       = fd.fun_defn_loc;
   fun_defn_aux       = signature}

(* Guesses whether the rule element [rle] is composed of only regexps.
   Since no environment is provided, it assumes any non-terminals are
   not regular expressions. *)
let rec guess_is_regexp_elem rle =
  match rle.rule_elem with
    | RE_epsilon
      | RE_regexp _
      | RE_action _
      | RE_constraint _ -> true

    | RE_named (_, rle')
      | RE_star (rle', _)
      | RE_opt rle'
      | RE_at_pos (_, rle')
      | RE_at_buf (_, rle') -> guess_is_regexp_elem rle'

    | RE_choice rles
      | RE_seq rles -> List.for_all guess_is_regexp_elem rles

    | RE_non_term _
    | RE_map_bufs _ -> false

(* Checks whether the rule element [rle] is composed of only regexps.
   Since an environment is provided, it looks up the types of any
   non-terminals to check whether they are regular expressions. *)
let rec is_regexp_elem tenv rle =
  match rle.rule_elem with
    | RE_epsilon
      | RE_regexp _
      | RE_action _
      | RE_constraint _ -> true

    | RE_named (_, rle')
      | RE_star (rle', _)
      | RE_opt rle'
      | RE_at_pos (_, rle')
      | RE_at_buf (_, rle') -> is_regexp_elem tenv rle'

    | RE_choice rles
      | RE_seq rles -> List.for_all (is_regexp_elem tenv) rles

    | RE_non_term (nid, _) ->
        let n = Location.value nid in
        (match lookup_non_term_type tenv (NName n) with
           | Some t -> is_regexp_type (typcon_variable tenv) t
           | None -> false
        )

    | RE_map_bufs _ -> false

(** [infer_nt_rhs_type tenv ntd] tries to deduce a type for the
    right-hand side of the definition of [ntd]. This is done
    in the following cases:
    . there is a single production with a single non-terminal
      - the inferred type is the type of that non-terminal
    . all the productions are regular expressions
      - the inferred type is a list of bytes
    There cannot be any action elements, and any constraint elements
    are ignored.

    TODO: this could be extended, e.g. for the above under a star or option
    operator, or restricted to views, etc.
 *)
let infer_nt_rhs_type tenv ntd =
  let res =
    match ntd.non_term_rules with
      (* a single production with a single non-terminal *)
      | [{rule_rhs = [{rule_elem = RE_non_term (n, _); _}]; _}] ->
          lookup_non_term_type tenv (NName (Location.value n))
      (* each production is a sequence of unnamed regular expressions *)
      | rules ->
          let is_regexp =
            List.for_all (fun r ->
                List.for_all guess_is_regexp_elem r.rule_rhs
              ) rules in
          if is_regexp then
            let byte  = typcon_variable tenv (TName "byte") in
            Some (list (typcon_variable tenv) byte)
          else
            None in
  match res with
    | Some t -> t
    | None ->
        raise (Error (NTTypeNotInferrable ntd.non_term_name))

let infer_non_term_attrs tenv nid attrs =
  List.fold_left (fun ats (pid, te) ->
      let p  = Location.value pid in
      let te = AstUtils.expand_type_abbrevs tenv te in
      let t  = TypeConv.intern tenv te in
      match StringMap.find_opt p ats with
        | Some (_, l) ->
            let repid = Location.mk_loc_val p l in
            raise (Error (NTRepeatedBinding (nid, pid, repid)))
        | None ->
            StringMap.add p (t, Location.loc pid) ats
    ) StringMap.empty attrs

let infer_non_term_inh_type tenv ntd =
  let nid = ntd.non_term_name in
  let attrs = ntd.non_term_inh_attrs in
  infer_non_term_attrs tenv nid attrs

(** [infer_non_term_type tenv ctxt ntd] updates [tenv] with a record
   type for a non-terminal (NT) [ntd] corresponding to its synthesized
   attributes, and updates ctxt with the names of the corresponding
   field destructors. *)
let infer_non_term_type tenv ctxt ntd =
  let ntid  = ntd.non_term_name
  and loc   = ntd.non_term_loc in
  let ntnm  = Location.value ntid
  and ntpos = Location.loc ntid in
  let inh_typ = infer_non_term_inh_type tenv ntd in
  match ntd.non_term_syn_attrs with
    | ALT_type t ->
        (* t should be a record type, and the NT should be
           given a flexible variable which is equated to [[t]]. *)
        let tn = Location.value t in
        let tloc = Location.loc t in
        if not (is_record_type tenv (TName tn)) then
          raise (Error (NTAttributesNotRecordType (ntid, t)));
        let tvar  = lookup_type_variable ~pos:tloc tenv (TName tn) in
        (* This NT cannot be used as a type constructor since it is
           aliased to the defined type, and it is represented by a
           flexible variable to create a solvable constraint. If we
           need to use NT as a type constructor, we will have to
           modify the tycon lookup logic in the typing environment
           to not require Constant variables. *)
        let ivar  = variable ~name:(TName ntnm) Flexible () in
        let cnstr = (CoreAlgebra.TVariable ivar =?= tvar) tloc in
        let ntt   = (inh_typ, NTT_type (CoreAlgebra.TVariable ivar)) in
        let tenv' = add_non_terminal tenv ntpos (NName ntnm) ntt in
        let ctxt' = (fun c ->
            ctxt (CLet ([Scheme (loc, [], [ivar], cnstr ^ c, StringMap.empty)],
                        CTrue loc))
          ) in
        tenv', ctxt'
    | ALT_decls [] ->
        (* No type is declared; so it needs to be inferred.  This NT
           cannot be used as a type constructor. *)
        let tvar  = infer_nt_rhs_type tenv ntd in
        let ivar  = variable ~name:(TName ntnm) Flexible () in
        let cnstr = (CoreAlgebra.TVariable ivar =?= tvar) ntd.non_term_loc in
        let ntt   = (inh_typ, NTT_type (CoreAlgebra.TVariable ivar)) in
        let tenv' = add_non_terminal tenv ntpos (NName ntnm) ntt in
        let ctxt' = (fun c ->
            ctxt (CLet ([Scheme (loc, [], [ivar], cnstr ^ c, StringMap.empty)],
                        CTrue loc))
          ) in
        tenv', ctxt'
    | ALT_decls attrs ->
        (* The NT is given a new monomorphic record type corresponding
           to the explicitly declared attributes.  This allows the NT
           to be usable as a type constructor. *)
        let ikind = KindInferencer.intern_kind (as_kind_env tenv) KStar in
        let ivar  = variable ~name:(TName ntnm) Constant () in
        let adt   = ref None in
        let tenv  = add_type_constructor tenv ntpos (TName ntnm)
                      (ikind, ivar, adt) in
        let rcd   = ref None in
        let ntt   = (inh_typ, NTT_record (ivar, rcd)) in
        let tenv' = add_non_terminal tenv ntpos (NName ntnm) ntt in
        let ctxt' = (fun c ->
            ctxt (CLet ([Scheme (loc, [ivar], [], c, StringMap.empty)],
                        CTrue loc))
          ) in
        let attrs = List.map (fun (id, te, _) ->
                        id, AstUtils.expand_type_abbrevs tenv te
                      ) attrs in
        let tenv', dids, drqs, let_env =
          List.fold_left
            (intern_field_destructor ntid [])
            (tenv', [], [], StringMap.empty)
            attrs in
        let tenv', cid, crqs, let_env =
          intern_record_constructor ntid []
            (tenv', let_env) attrs in
        let fields, _ = List.split attrs in
        let rec_info = {adt = ntid;
                        fields;
                        record_constructor = cid;
                        field_destructors = dids} in
        rcd := Some rec_info;
        adt := Some {adt = Record rec_info; loc};
        let ctxt' = (fun c ->
            ctxt' (CLet ([Scheme (loc, drqs @ crqs, [], CTrue loc, let_env)],
                         c))
          ) in
        tenv', ctxt'

let check_non_term tenv id t =
  let n = Location.value id in
  match lookup_non_term_type tenv (NName n) with
    | None ->
        raise (Error (UnknownNonTerminal id))
    | Some t' ->
        (t =?= t') (Location.loc id)

let rec check_literals tenv ls t =
  match ls.literal_set with
    | LS_type id ->
        (* This non-terminal should have byte list type *)
        check_non_term tenv id t
    | LS_diff (l, r) ->
        (check_literals tenv l t) ^ (check_literals tenv r t)
    | LS_set _ | LS_range (_, _) ->
        (* Literals will always be byte lists *)
        let byte  = typcon_variable tenv (TName "byte") in
        let bytes = list (typcon_variable tenv) byte in
        (t =?= bytes) ls.literal_set_loc

let rec infer_regexp tenv re t =
  let byte    = typcon_variable tenv (TName "byte") in
  let bytes   = list (typcon_variable tenv) byte in
  let default = (t =?= bytes) re.regexp_loc in
  let mk_auxregexp re' =
    {regexp = re'; regexp_loc = re.regexp_loc; regexp_aux = t} in
  match re.regexp with
    | RX_literals ls ->
        check_literals tenv ls bytes, mk_auxregexp (RX_literals ls)
    | RX_wildcard ->
        default, mk_auxregexp RX_wildcard
    | RX_type id ->
        (* This non-terminal should have a byte list type *)
        check_non_term tenv id bytes,
        mk_auxregexp (RX_type id)

    (* The typing of Star here assumes that the individual matches for
       [re'] can be flattened into a byte list type for [re' *].  That
       is, if [re'] |- list byte, then [re' *] |- list byte due to the
       flattening.  To achieve this, we only need to ensure that [re']
       can be typed for some [t'], and ensure that the types of the
       base cases of RX_ are byte lists. *)
    | RX_star (re', None) ->
        let c, re'' =
          exists_aux (fun t' -> infer_regexp tenv re' t') in
        c ^ default,
        mk_auxregexp (RX_star (re'', None))
    | RX_star (re', Some e) ->
        let int = typcon_variable tenv (TName "int") in
        let ce, e' = infer_expr tenv e int in
        let cre, re'' = exists_aux (fun t' -> infer_regexp tenv re' t') in
        ce ^ cre ^ default,
        mk_auxregexp (RX_star (re'', Some e'))

    | RX_opt re' ->
        let c, re'' = infer_regexp tenv re' t in
        c, mk_auxregexp (RX_opt re'')

    (* For the same reasons as for Star above, we only ensure that the
       individual matches can be typed, and provide a byte list type
       for the overall type. *)
    | RX_choice rels ->
        exists_list_aux rels (fun exs ->
            let rels' =
              List.map (fun (re', t') -> infer_regexp tenv re' t') exs in
            let cs, rels' = List.split rels' in
            conj cs ^ default,
            mk_auxregexp (RX_choice rels')
          )
    | RX_seq rels ->
        exists_list_aux rels (fun exs ->
            let rels' =
              List.map (fun (re', t') -> infer_regexp tenv re' t') exs in
            let cs, rels' = List.split rels' in
            conj cs ^ default,
            mk_auxregexp (RX_seq rels')
          )

let rec infer_stmt tenv s =
  let make_stmt s' = {stmt = s'; stmt_loc = s.stmt_loc} in
  match s.stmt with
    | S_assign (l, r) ->
        (* Ensure that there is a type [t'] that is compatible with
           both sides of the assignment. *)
        exists_aux (fun t' ->
            let cl, l' = infer_expr tenv l t' in
            let cr, r' = infer_expr tenv r t' in
            cl ^ cr, make_stmt (S_assign (l', r')))
    | S_let (p, def, ss) ->
        (* Similar to E_let. *)
        exists_aux (fun t' ->
            let fragment, p' = infer_pat_fragment tenv p t' in
            let cdef, def' = infer_expr tenv def t' in
            let css, ss' = List.split (List.map (infer_stmt tenv) ss) in
            cdef
            ^ CLet ([ Scheme (s.stmt_loc, [], fragment.vars,
                              fragment.tconstraint,
                              fragment.gamma) ],
                    conj css),
            make_stmt (S_let (p', def', ss')))
    | S_case (e, clauses) ->
        (* Similar to E_case *)
        (* TODO: pattern exhaustiveness checks. *)
        exists_aux (fun t' ->
            let ce, e' = infer_expr tenv e t' in
            let clauses' =
              List.map
                (fun (p, ss) ->
                  let fragment, p' = infer_pat_fragment tenv p t' in
                  let css, ss' =
                    List.split (List.map (infer_stmt tenv) ss) in
                  CLet ([ Scheme (p.pattern_loc, [], fragment.vars,
                                  fragment.tconstraint,
                                  fragment.gamma) ],
                        conj css),
                  (p', ss'))
                clauses in
            let ccl, clauses' = List.split clauses' in
            ce ^ conj ccl,
            make_stmt (S_case (e', clauses')))

let infer_action tenv act t =
  (* [t] can only bind the last expression if any of the sequence,
   * otherwise it should equal [unit]. *)
  let ss, e = act.action_stmts in
  let css, ss' = List.split (List.map (infer_stmt tenv) ss) in
  let ce, e' = match e with
      | None ->
          let u = typcon_variable tenv (TName "unit") in
          (t =?= u) act.action_loc, None
      | Some e ->
          let c, e' = infer_expr tenv e t in
          c, Some e' in
  conj css ^ ce,
  {action_stmts = (ss', e'); action_loc = act.action_loc}

(** [bound] tracks whether this rule_elem is under a binding.
    This affects the typing of the '|' choice operator:
      a=( ... (re | re') ... )
    requires [re] and [re'] to receive the same type, which does not
    apply to an unbound choice
      ... (re | re') ...
    where re and re' can receive different types.
 *)
let rec infer_rule_elem tenv ntd ctx re t bound : context * crterm rule_elem =
  let pack_constraint c' =
    (fun c -> ctx (c' ^ c)) in
  let mk_regexp_type () =
    let byte = typcon_variable tenv (TName "byte") in
    list (typcon_variable tenv) byte in
  let mk_aux_rule_elem re' =
    {rule_elem = re'; rule_elem_loc = re.rule_elem_loc; rule_elem_aux = t} in
  match re.rule_elem with
    | RE_regexp r ->
        let c, r' = infer_regexp tenv r t in
        pack_constraint c,
        mk_aux_rule_elem (RE_regexp r')
    | RE_non_term (nid, None) ->
        (let n = Location.value nid in
         match lookup_non_term tenv (NName n) with
           | None ->
               raise (Error (UnknownNonTerminal nid))
           | Some (inh, syn) ->
               (* Check if inherited attributes need to be specified. *)
               (match StringMap.choose_opt inh with
                  | None ->
                      let c = (t =?= syn) re.rule_elem_loc in
                      pack_constraint c,
                      mk_aux_rule_elem (RE_non_term (nid, None))
                  | Some (id, _) ->
                      raise (Error (NTInheritedUnspecified (nid, id))))
        )
    | RE_non_term (cntid, Some attrs) ->
        let cntn = Location.value cntid in
        let cnti = match lookup_non_term tenv (NName cntn) with
            | None -> raise (Error (UnknownNonTerminal cntid))
            | Some (inh_typ, _) -> inh_typ in
        let pids, cs, attrs' =
          List.fold_left (fun (pids, cs, attrs') (pid, e) ->
              let pn = Location.value pid in
              let pids = match StringMap.find_opt pn pids with
                  | Some repid ->
                      raise (Error (NTRepeatedBinding (cntid, pid, repid)))
                  | None ->
                      StringMap.add pn pid pids in
              let typ = match StringMap.find_opt pn cnti with
                  | Some (typ, _) ->
                      typ
                  | None ->
                      raise (Error (NTUnknownInheritedAttribute (cntid, pid))) in
              let c, e' = infer_expr tenv e typ in
              pids, c :: cs, (pid, e') :: attrs'
            ) (StringMap.empty, [], []) attrs in
        StringMap.iter (fun pn _ ->
            if not (StringMap.mem pn pids)
            then raise (Error (NTInheritedUnspecified (cntid, pn)))
          ) cnti;
        pack_constraint (conj cs),
        mk_aux_rule_elem (RE_non_term (cntid, Some attrs'))
    | RE_constraint e ->
        let b = typcon_variable tenv (TName "bool") in
        let c, e' = infer_expr tenv e b in
        let c = (t =?= b) re.rule_elem_loc ^ c in
        pack_constraint c,
        mk_aux_rule_elem (RE_constraint e')
    | RE_action a ->
        let c, a' = infer_action tenv a t in
        pack_constraint c,
        mk_aux_rule_elem (RE_action a')
    | RE_named (id, re') ->
        (* [id] is bound in the environment when typing [re'] *)
        let idloc = Location.loc id in
        let id'   = Location.value id in
        (* re' needs to be typed under a binding *)
        let ctx', re'' = infer_rule_elem tenv ntd (fun c -> c) re' t true in
        (fun c ->
          ctx (CLet ([Scheme (re.rule_elem_loc, [], [],
                              CTrue re.rule_elem_loc,
                              StringMap.singleton id' (t, idloc))],
                     ctx' c))),
        mk_aux_rule_elem (RE_named (id, re''))

    | RE_seq rels ->
        (* A sequence has a tuple type formed from the individual rule
           elements, unless they are all regexps, in which case they
           are flattened. *)
        let is_regexp = List.for_all (is_regexp_elem tenv) rels in
        let qs, m = variable_list Flexible rels in
        let ctx', rels' =
          List.fold_left (fun (ctx', rels') (re, t') ->
              let ctx', re' =
                infer_rule_elem tenv ntd ctx' re t' bound in
              ctx', re' :: rels'
            ) ((fun c -> c), []) m in
        let typ =
          if is_regexp then mk_regexp_type ()
          else tuple (typcon_variable tenv) (snd (List.split m)) in
        (fun c ->
          ctx (ex ~pos:re.rule_elem_loc qs
                 ((t =?= typ) re.rule_elem_loc ^ ctx' c))),
        mk_aux_rule_elem (RE_seq rels')

    | RE_choice rels when List.for_all (is_regexp_elem tenv) rels ->
        (* If the sequence is composed purely of regexps, flatten into
           a single byte list, after ensuring each element is
           well-typed. *)
        let qs, m = variable_list Flexible rels in
        let ctx', rels' =
          List.fold_left (fun (ctx', rels') (re, t') ->
              let ctx', re' =
                infer_rule_elem tenv ntd ctx' re t' bound in
              ctx', re' :: rels'
            ) ((fun c -> c), []) m in
        let typ = mk_regexp_type () in
        (fun c ->
          ctx (ex ~pos:re.rule_elem_loc qs
                 ((t =?= typ) re.rule_elem_loc) ^ ctx' c)),
        mk_aux_rule_elem (RE_choice rels')
    | RE_choice rels ->
        if bound then
          (* Each choice should have the same type [t]. *)
          let ctx', rels' =
            List.fold_left (fun (ctx', rels') re ->
                let ctx', re' =
                  infer_rule_elem tenv ntd ctx' re t bound in
                ctx', re' :: rels'
              ) ((fun c -> c), []) rels in
          (fun c -> ctx (ctx' c)),
          mk_aux_rule_elem (RE_choice rels')
        else
          (* Each choice can receive a different type, and [t] is unconstrained *)
          let qs, m = variable_list Flexible rels in
          let ctx', rels' =
            List.fold_left (fun (ctx', rels') (re, t') ->
                let ctx', re' =
                  infer_rule_elem tenv ntd ctx' re t' bound in
                ctx', re' :: rels'
              ) ((fun c -> c), []) m in
          (fun c ->
            ctx (ex ~pos:re.rule_elem_loc qs (ctx' c))),
          mk_aux_rule_elem (RE_choice rels')

    | RE_star (re', None) ->
        (* [re] has a type [list t'] where [t'] is the type of [re'],
           unless [re'] is a regexp, in which case it is flattened. *)
        let is_regexp = is_regexp_elem tenv re' in
        let q  = variable Flexible () in
        let t' = CoreAlgebra.TVariable q in
        let ctx', re'' =
          infer_rule_elem tenv ntd (fun c -> c) re' t' bound in
        let typ = if is_regexp
                  then mk_regexp_type ()
                  else list (typcon_variable tenv) t' in
        (fun c ->
          ctx (ex ~pos:re.rule_elem_loc [q]
                 ((t =?= typ) re.rule_elem_loc ^ ctx' c))),
        mk_aux_rule_elem (RE_star (re'', None))
    | RE_star (re', Some e) ->
        (* [re] has a type [list t'] where [t'] is the type of [re']
           (unless [re'] is a regexp) and [e] has type int *)
        let is_regexp = is_regexp_elem tenv re' in
        let int = typcon_variable tenv (TName "int") in
        let q  = variable Flexible () in
        let t' = CoreAlgebra.TVariable q in
        let ctx', re'' =
          infer_rule_elem tenv ntd (fun c -> c) re' t' bound in
        let typ = if is_regexp
                  then mk_regexp_type ()
                  else list (typcon_variable tenv) t' in
        let ce, e' = infer_expr tenv e int in
        (fun c ->
          ctx (ex ~pos:re.rule_elem_loc [q]
                 ((t =?= typ) re.rule_elem_loc ^ ce ^ ctx' c))),
        mk_aux_rule_elem (RE_star (re'', Some e'))

    | RE_opt re' ->
        (* [re] has a type [option t'] where [t'] is the type of [re']
           (unless [re'] is a regexp) *)
        let is_regexp = is_regexp_elem tenv re' in
        let q  = variable Flexible () in
        let t' = CoreAlgebra.TVariable q in
        let ctx', re'' =
          infer_rule_elem tenv ntd (fun c -> c) re' t' bound in
        let typ = if is_regexp
                  then mk_regexp_type ()
                  else option (typcon_variable tenv) t' in
        (fun c ->
          ctx (ex ~pos:re.rule_elem_loc [q]
                 ((t =?= typ) re.rule_elem_loc ^ ctx' c))),
        mk_aux_rule_elem (RE_opt re'')

    | RE_epsilon ->
        let u = typcon_variable tenv (TName "unit") in
        let c = (t =?= u) re.rule_elem_loc in
        pack_constraint c,
        mk_aux_rule_elem RE_epsilon

    | RE_at_pos (e, re') ->
        (* [pos] needs to be an integer and [re'] should have type [t] *)
        let int = typcon_variable tenv (TName "int") in
        let ce, e' = infer_expr tenv e int in
        let ctx', re'' =
          infer_rule_elem tenv ntd (fun c -> c) re' t bound in
        (fun c -> ctx (ce ^ ctx' c)),
        mk_aux_rule_elem (RE_at_pos (e', re''))
    | RE_at_buf (buf, re') ->
        (* [buf] should have type [view] and [re'] should have type [t] *)
        let view = typcon_variable tenv (TName "view") in
        let cb, buf' = infer_expr tenv buf view in
        let ctx', re'' =
          infer_rule_elem tenv ntd (fun c -> c) re' t bound in
        (fun c -> ctx (cb ^ ctx' c)),
        mk_aux_rule_elem (RE_at_buf (buf', re''))
    | RE_map_bufs (bufs, re') ->
        (* [bufs] should have type [list view] and [re] should have
         * type [list t'] where [t'] is the type of [re'] *)
        let view = typcon_variable tenv (TName "view") in
        let views = list (typcon_variable tenv) view in
        let cb, bufs' = infer_expr tenv bufs views in
        let q  = variable Flexible () in
        let t' = CoreAlgebra.TVariable q in
        let ctx', re'' =
          infer_rule_elem tenv ntd (fun c -> c) re' t' bound in
        let result = list (typcon_variable tenv) t' in
        (fun c ->
          ctx (ex ~pos:re.rule_elem_loc [q]
                 cb ^ (t =?= result) re.rule_elem_loc ^ ctx' c)),
        mk_aux_rule_elem (RE_map_bufs (bufs', re''))

let infer_non_term_rule tenv ntd rule pids =
  (* add temporaries to local bindings *)
  let _pids, bindings, temps' =
    List.fold_left (fun (pids, fragment, temps) (pid, typ, exp) ->
        let pn, ploc = Location.value pid, Location.loc pid in
        let pids =
          match StringMap.find_opt pn pids with
            | Some repid ->
                raise (Error (NTRepeatedBinding (ntd.non_term_name, pid, repid)))
            | None ->
                StringMap.add pn pid pids in
        let ityp = TypeConv.intern tenv typ in
        let v = variable Flexible () in
        let cexp, exp' = infer_expr tenv exp ityp in
        let temp = pid, typ, exp' in
        pids,
        {gamma = StringMap.add pn (CoreAlgebra.TVariable v, ploc)
                   fragment.gamma;
         tconstraint = (CoreAlgebra.TVariable v =?= ityp) ploc
                       ^ cexp
                       ^ fragment.tconstraint;
         vars = v :: fragment.vars},
        temp :: temps
      ) (pids, empty_fragment, []) rule.rule_temps in
  let qs, ctx, rhs' =
    List.fold_left (fun (qs, ctx, rhs') re ->
        let q  = variable Flexible () in
        let t' = CoreAlgebra.TVariable q in
        let ctx', re' = infer_rule_elem tenv ntd ctx re t' false in
        q :: qs, ctx', re' :: rhs'
      ) ([], (fun c -> c), []) rule.rule_rhs in
  CLet ([ Scheme (rule.rule_loc, [],
                  bindings.vars,
                  bindings.tconstraint,
                  bindings.gamma) ],
        (ex ~pos:rule.rule_loc qs (ctx (CTrue rule.rule_loc)))),
  {rule_rhs = List.rev rhs'; rule_temps = temps'; rule_loc = rule.rule_loc}

let infer_non_term tenv ntd =
  let ntid = NName (Location.value ntd.non_term_name) in
  let inh_attrs = match lookup_non_term tenv ntid with
      | None ->
          (* the type definition is processed in the previous typing
             pass and should already be present *)
          assert false
      | Some (i, _) -> i in

  (* If there are any initializers for the synthesized attributes,
   * collect their typing constraints.
   *)
  let csyn_attrs, non_term_syn_attrs =
    match ntd.non_term_syn_attrs with
      | ALT_type t ->
          [], ALT_type t
      | ALT_decls d ->
          let c, d' =
            List.fold_left (fun (cs, ds) (pid, typ, exp) ->
                match exp with
                  | None ->
                      cs, (pid, typ, None) :: ds
                  | Some e ->
                      let ityp = TypeConv.intern tenv typ in
                      let c, e' = infer_expr tenv e ityp in
                      c :: cs, (pid, typ, Some e') :: ds
              ) ([], []) d in
          c, ALT_decls (List.rev d') in
  (* compute the local bindings for each rule: this includes any
   * name for the non-terminal itself, along with the bindings
   * for the inherited attributes.
   *)
  let pids, bindings = match ntd.non_term_varname with
      | None ->
          StringMap.empty, empty_fragment
      | Some n ->
          let nloc = Location.loc n in
          let ntt  = match lookup_non_term_type tenv ntid with
              | None -> assert false
              | Some t -> t in
          let v = variable Flexible () in
          StringMap.singleton (Location.value n) n,
          {gamma = StringMap.singleton (Location.value n)
                     (CoreAlgebra.TVariable v, nloc);
           tconstraint = (CoreAlgebra.TVariable v =?= ntt) nloc;
           vars = [ v ]} in
  let pids, bindings =
    List.fold_left (fun (pids, fragment) (pn, (ityp, ploc)) ->
        let pid = Location.mk_loc_val pn ploc in
        let pids =
          match StringMap.find_opt pn pids with
            | Some repid ->
                raise (Error (NTRepeatedBinding (ntd.non_term_name, pid, repid)))
            | None ->
                StringMap.add pn pid pids in
        let v = variable Flexible () in
        pids,
        {gamma = StringMap.add pn (CoreAlgebra.TVariable v, ploc)
                   fragment.gamma;
         tconstraint = (CoreAlgebra.TVariable v =?= ityp) ploc
                       ^ fragment.tconstraint;
         vars = v :: fragment.vars}
      ) (pids, bindings) (StringMap.bindings inh_attrs) in
  let crules' = List.map
                 (fun r -> infer_non_term_rule tenv ntd r pids)
                 ntd.non_term_rules in
  let cs, rules' = List.split crules' in
  let cprod =
    CLet ([ Scheme (ntd.non_term_loc, [],
                    bindings.vars,
                    bindings.tconstraint,
                    bindings.gamma) ],
          conj cs) in
  (conj csyn_attrs) ^ cprod,
  {non_term_name      = ntd.non_term_name;
   non_term_varname   = ntd.non_term_varname;
   non_term_inh_attrs = ntd.non_term_inh_attrs;
   non_term_syn_attrs = non_term_syn_attrs;
   non_term_rules     = rules';
   non_term_loc       = ntd.non_term_loc}

(** Initialize the typing environment with the builtin types and
    constants. *)
let init_tenv () =
  let mk_variable = (fun ?name () -> variable Rigid ?name:name ()) in
  let init_builtin_types types =
    List.rev (
        Array.fold_left
          (fun acu (o, (arity, ds)) ->
            (o, (arity,
                 CoreAlgebra.TVariable (mk_variable ?name:(Some o) ()),
                 ds)
            ) :: acu)
          [] types) in
  let builtin_types = init_builtin_types builtin_types in

  (* Add the builtin data constructors into the environment.  The
     builtins currently only use variant algebraic types. *)
  let init_ds (TName adt_name) env_info ds =
    let adt_id = Location.mk_ghost adt_name in
    let (_tenv, dcs, _lrqs, _let_env) as env_info =
      List.fold_left
        (fun env_info (DName d, qs, ty) ->
          let qs = List.map (fun (TName q) -> Location.mk_ghost q) qs in
          let d = Location.mk_ghost d in
          intern_data_constructor true adt_id qs env_info (d, Some ty)
        ) env_info ds in
    (dcs, env_info) in

  (* Compute the scheme of a builtin constant. *)
  let intern_const tenv qs typ =
    let rqs, rtenv = fresh_unnamed_rigid_vars Location.ghost_loc tenv qs in
    let tenv' = add_type_variables rtenv tenv in
    let ityp = TypeConv.intern tenv' typ in
    rqs, ityp in

  (* For each builtin datatype, add a type constructor and any
     associated data constructors into the environment. *)
  let intern_type tenv let_env (n, (kind, _v, ds)) =
    let gloc = Location.ghost_loc in
    let r = ref None in
    let tvar = variable ~name:n Constant () in
    let tenv = add_type_constructor tenv gloc n
                 (KindInferencer.intern_kind (as_kind_env tenv) kind,
                  tvar,
                  r) in
    let (dcs, env_info) =
      init_ds n (tenv, [], [], let_env) ds in
    (* If there are no data constructors, it does not need any adt_info. *)
    if List.length dcs > 0
    then r := Some {adt = Variant dcs; loc = gloc};
    env_info in

  let intern_types tenv let_env builtins =
    List.fold_left
      (fun (tenv, lrqs, let_env) btyp ->
        let (tenv, _, lrqs', let_env) =
          intern_type tenv let_env btyp in
        tenv, lrqs' @ lrqs, let_env
      ) (tenv, [], let_env) builtins in

  (* Register the builtin types. *)
  let (init_tenv, lrqs, let_env) =
    intern_types empty_environment StringMap.empty builtin_types in

  (* Update with the builtin constants. *)
  let lrqs, let_env =
    Array.fold_left (fun (lrqs, let_env) (DName c, qs, typ) ->
        let rqs, ityp = intern_const init_tenv qs typ in
        rqs @ lrqs,
        StringMap.add c (ityp, Location.ghost_loc) let_env
      ) (lrqs, let_env) builtin_consts in

  (* Update with the builtin module values. *)
  let init_tenv, lrqs, let_env =
    let builtin_loc = Location.ghost_loc in
    List.fold_left (fun (tenv, lrqs, let_env) minfo ->
        (List.fold_left
           (fun (tenv, lrqs, let_env)
                ((DName vid) as v, qs, typ) ->
             (* Encode the item name as it appears in the source. *)
             let MName mid = minfo.mod_name in
             let id = Printf.sprintf "%s.%s" mid vid in
             let rqs, ityp = intern_const tenv qs typ in
             add_mod_item tenv builtin_loc minfo.mod_name v (rqs, ityp),
             rqs @ lrqs,
             StringMap.add id (ityp, builtin_loc) let_env
           ) (tenv, lrqs, let_env) minfo.mod_values)
      ) (init_tenv, lrqs, let_env) builtin_modules in

  (* Update with the builtin non-terminals.  These are implemented
     with primitive builtin types and do not have any inherited
     attributes. *)
  let init_tenv =
    Array.fold_left (fun tenv ((NName n) as nt, inh_attrs, typ) ->
        let gloc = Location.ghost_loc in
        let nid = Location.mk_ghost n in
        let typ = TypeConv.intern tenv typ in
        let syn_typ = NTT_type typ in
        let inh_typ = infer_non_term_attrs tenv nid inh_attrs in
        let ntt = (inh_typ, syn_typ) in
        add_non_terminal tenv gloc nt ntt
      ) init_tenv builtin_non_terms in

  (* Extract the variables bound to the type constructors. *)
  let vs =
    fold_type_info (fun vs (_n, (_, v, _)) -> v :: vs) [] init_tenv in

  (* The initial environment is implemented as a constraint context. *)
  init_tenv,
  (fun c ->
    CLet ([ Scheme (Location.ghost_loc, vs, [],
                    CLet ([ Scheme
                              (Location.ghost_loc, lrqs, [],
                               CTrue Location.ghost_loc,
                               let_env)
                          ],
                          c),
                    StringMap.empty) ],
          CTrue Location.ghost_loc))

let has_type_abbrevs tds =
  (* Switch to List.fold_map when OCaml 4.10 is more common. *)
  List.fold_left (fun res td ->
      match res with
        | Some _ -> res
        | None -> (
          let tr = td.type_decl_body in
          match tr.type_rep with
            | TR_defn _ -> Some td
            | _         -> None
        )
    ) None tds

let infer_spec tenv spec =
  (* First pass: process the expression language, and the
     type-definitions for the non-terminals, and collect their
     annotated versions *)
  let tenv, ctxt, decls =
    List.fold_left (fun (tenv, ctxt, decls) decl ->
        match decl with
          | Decl_types (tds, tdsloc) as d ->
              let decls' = d :: decls in
              (* If there are multiple declarations, they could be
                 mutually recursive.  If they contain type
                 abbreviations, expanding them may not terminate.  For
                 simplicity, we bar abbreviations from appearing in
                 potentially recursive declaration sets.  The
                 treatment of mutually non-recursive
                 (non-abbreviation) declarations as if they were
                 recursive still gives (trivially) the desired result.
               *)
              (match has_type_abbrevs tds with
                 | Some td ->
                     if List.length tds > 1 then
                       let id = td.type_decl_ident in
                       let err =
                         PotentiallyRecursiveTypeAbbreviation id in
                       raise (Error err)
                     else
                       let tenv' = infer_type_abbrev tenv td in
                       tenv', ctxt, decls'
                 | None ->
                     let tenv', ctxt =
                       infer_type_decls tenv ctxt tdsloc tds in
                     tenv', ctxt, decls'
              )
          | Decl_fun f ->
              (* TODO: solve eagerly? *)
              let c, f' = infer_fun_defn tenv ctxt f in
              tenv, c, Decl_fun f' :: decls
          | Decl_format f ->
              let tenv, ctxt =
                List.fold_left (fun (te, c) fd ->
                    let ntd = fd.format_decl in
                    infer_non_term_type te c ntd
                  ) (tenv, ctxt) f.format_decls in
              (* Annotate the grammar in the next pass *)
              tenv, ctxt, decls
      ) (tenv, (fun c -> c), []) spec.decls in

  (* Second pass: process the grammar spec comprising the rules for
     each non-terminal. *)
  let c', decls =
    List.fold_left (fun (c, decls) d ->
        match d with
          | Decl_format f ->
              let c, fds' =
                List.fold_left (fun (c, fds') fd ->
                    let ntd = fd.format_decl in
                    let c', ntd' = infer_non_term tenv ntd in
                    let fd' = {format_decl     = ntd';
                               format_attr     = fd.format_attr;
                               format_decl_loc = fd.format_decl_loc} in
                    c ^ c', fd' :: fds'
                  ) (c, []) f.format_decls in
              let f' = {format_decls = List.rev fds';
                        format_loc   = f.format_loc} in
              c,  Decl_format f' :: decls
          | _ ->
              c, decls
      ) ((CTrue Location.ghost_loc), decls) spec.decls in

  let ctxt = (fun c -> ctxt (c' ^ c)) in
  tenv, ctxt, {decls = List.rev decls}

let generate_constraint spec =
  let tenv, c = init_tenv () in
  let tenv', c', spec' = infer_spec tenv spec in
  c (c' (CDump Location.ghost_loc)), tenv', spec'
