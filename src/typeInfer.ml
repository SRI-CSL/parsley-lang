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
  {
    gamma       : (crterm * Location.t) StringMap.t;
    vars        : variable list;
    tconstraint : tconstraint;
  }

(** The [empty_fragment] is used when nothing has been bound. *)
let empty_fragment =
  {
    gamma       = StringMap.empty;
    vars        = [];
    tconstraint = CTrue Location.ghost_loc;
  }

(** Joining two fragments is straightforward except that the environments
    must be disjoint (a pattern cannot bound a variable several times). *)
let rec join_fragment pos f1 f2 =
  {
    gamma =
      (try
         StringMap.strict_union f1.gamma f2.gamma
       with StringMap.Strict x -> raise (Error (NonLinearPattern (pos, x))));
    vars        = f1.vars @ f2.vars;
    tconstraint = f1.tconstraint ^ f2.tconstraint;
  }

(** [infer_pat_fragment p t] generates a fragment that represents the
    information gained by a success when matching p. *)
and infer_pat_fragment tenv p t =
  let join pos = List.fold_left (join_fragment pos) empty_fragment in
  let rec infpat t p =
    let pos = p.pattern_loc in
    match p.pattern with
    (** Wildcard pattern does not generate any fragment. *)
    | P_wildcard ->
        empty_fragment

    (** We refer to the algebra to know the type of a primitive. *)
    | P_literal l ->
        { empty_fragment with
          tconstraint = (t =?= type_of_primitive (as_fun tenv) l) pos
        }

    (** Matching against a variable generates a fresh flexible variable,
        binds it to the [name] and forces the variable to be equal to [t]. *)
    | P_var name ->
        let pos = Location.loc name in
        let v = variable Flexible () in
        {
          gamma       = StringMap.singleton (Location.value name) (CoreAlgebra.TVariable v, pos);
          tconstraint = (CoreAlgebra.TVariable v =?= t) pos;
          vars        = [ v ]
        }

    (** Matching against a data constructor generates the fragment that:
        - forces [t] to be the type of the constructed value ;
        - constraints the types of the subpatterns to be equal to the arguments
        of the data constructor. *)
    | P_variant ((_typ, c), ps) ->
        let cid, cloc = Location.value c, Location.loc c in
        let alphas, ct = fresh_datacon_scheme tenv cloc (DName cid) in
        let rt = result_type (as_fun tenv) ct
        and ats = arg_types (as_fun tenv) ct in
        if List.length ps <> List.length ats then
          let err =
            InvalidPatternArgs (pos, c, List.length ats, List.length ps) in
          raise (Error (err))
        else
          let fragment = join pos (List.map2 infpat ats ps) in
          { fragment with
            tconstraint = fragment.tconstraint ^ (t =?= rt) pos ;
            vars        = alphas @ fragment.vars;
          }
    (* TODO: add record patterns *)
  in infpat t p

(** checks for consistency between the declarations and
    uses of type variables *)
let check_distinct_tvars typid qs =
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

let check_tvars_usage tenv t qs used_set =
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
let make_dc_signature adt tvars dc opt_arg =
  let tvars = List.map AstUtils.make_tvar_ident tvars in
  let res =
    if List.length tvars = 0
    then AstUtils.make_tvar_ident adt
    else AstUtils.make_type_app_name (Location.value adt) tvars
           (Location.loc adt) in
  match opt_arg with
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
  let v = variable ~structure:ityp Flexible () in
  ((add_data_constructor tenv pos (TName adt_name) (DName dname)
      (TypeConv.arity typ, rqs, ityp)),
   (DName dname, v) :: acu,
   (rqs @ lrqs),
   StringMap.add dname (ityp, pos) let_env)

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
  let constructor, fields = make_record_signature adt_id qs fields in
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

(** [infer_type_decl examines a type declaration [td] within a
   typing environment [tenv] and a constraint context [ctxt], and
   returns updated typing and constraint contexts
 *)
let infer_type_decl tenv ctxt td =
  let ident = td.type_decl_ident in
  let name  = Location.value ident
  and kind  = td.type_decl_kind
  and tvars = td.type_decl_tvars
  and pos   = td.type_decl_loc
  and adt   = ref None in
  let ikind = KindInferencer.intern_kind (as_kind_env tenv) kind in
  let register_tycon ctx ?structure () =
    let ivar  = variable ~name:(TName name) ?structure Constant () in
    let tenv  = add_type_constructor tenv pos (TName name) (ikind, ivar, adt) in
    let ctxt' = (fun c ->
        ctx (CLet ([Scheme (pos, [ivar], [], c, StringMap.empty)],
                   CTrue pos))) in
    (tenv, ctxt') in
  let typ   = td.type_decl_body in
  check_distinct_tvars ident tvars;
  let tenv, rqs, let_env, ctxt' =
    match typ.type_rep with
      | TR_variant dcons ->
          let dcons =
            List.map (function
                | d, None ->
                    d, None
                | d, Some te ->
                    d, Some (AstUtils.expand_type_abbrevs tenv te)
              ) dcons in
          let tenv, ctxt = register_tycon ctxt () in
          let tenv, ids, rqs, let_env =
            List.fold_left
              (intern_data_constructor false ident tvars)
              (tenv, [], [], StringMap.empty)
              dcons in
          adt := Some { adt = Variant ids;
                        loc = pos };
          tenv, rqs, let_env, ctxt
      | TR_record fields ->
          let fields =
            List.map (fun (f, te) ->
                f, AstUtils.expand_type_abbrevs tenv te
              ) fields in
          let tenv, ctxt = register_tycon ctxt () in
          let tenv, dids, drqs, let_env =
            List.fold_left
              (intern_field_destructor ident tvars)
              (tenv, [], [], StringMap.empty)
              fields in
          let tenv, cid, crqs, let_env =
            intern_record_constructor ident tvars
              (tenv, let_env) fields in
          let fields, _ = List.split fields in
          adt := Some { adt = Record { adt = ident;
                                       fields;
                                       record_constructor = cid;
                                       field_destructors = dids };
                        loc = pos };
          tenv, drqs @ crqs, let_env, ctxt
      | TR_defn d ->
          let d' = AstUtils.expand_type_abbrevs tenv d in
          check_valid_type_defn tenv ident tvars d';
          let tvs =
            List.map (fun tv -> TName (Location.value tv)) tvars in
          let abb = { type_abbrev_tvars = tvs;
                      type_abbrev_type = d' } in
          let tenv' = add_type_abbrev tenv pos (TName name) abb in
          tenv', [], StringMap.empty, ctxt in
  let ctxt = (fun c ->
      ctxt' (CLet ([Scheme (pos, rqs, [], CTrue pos, let_env)],
                   c))) in
  (tenv, ctxt)

let make_match_case_expr exp typ dcon arity loc =
  let wc = AstUtils.make_pattern_loc P_wildcard loc in
  let mk_var s =
    let v = E_var (Location.mk_loc_val s loc) in
    AstUtils.make_expr_loc v loc in
  let rec mk_pats pats cnt =
    if cnt = 0 then pats else mk_pats (wc::pats) (cnt - 1) in
  let pargs = mk_pats [] arity in
  let pattern = AstUtils.make_pattern_loc (P_variant ((typ, dcon), pargs)) loc in
  let tr, fl = mk_var "true", mk_var "false" in
  let case_exp = E_case (exp, [pattern, tr; wc, fl]) in
  { expr = case_exp; expr_loc = loc }

(** looks up the adt in [tenv] matching the [fields] in a literal
    record expression; it reports mismatch errors at location [loc]. *)
let lookup_record_adt tenv fields =
  let f = List.hd fields in (* nonempty list is ensured in the parser *)
  let fid = Location.value f in
  let adtid = match lookup_field_adt tenv (LName fid) with
      | Some adtid -> adtid
      | None -> raise (Error (UnboundRecordField (Location.loc f, LName fid))) in
  let rec_info, rec_loc = match lookup_adt tenv adtid with
      | Some { adt = Record rec_info; loc = rec_loc } ->
          rec_info, rec_loc
      | Some { adt = Variant _ } ->
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
let rec infer_expr tenv e (t : crterm) =
  match e.expr with
    | E_var id ->
        (** The type of a variable must be at least as general as [t]. *)
        (SName (Location.value id) <? t) (Location.loc id)
    | E_constr (adt, dcon, args) ->
        (** A data constructor application is similar to the usual
            application except that it must be fully applied. *)
        let dcid, dcloc = Location.value dcon, Location.loc dcon in
        let arity, _, _ = lookup_datacon tenv dcloc (DName dcid) in
        let nargs = List.length args in
        if nargs <> arity then
          raise (Error (PartialDataConstructorApplication (dcon, arity, nargs)))
        else
          exists_list args (
              fun exs ->
              let typ, c = List.fold_left
                             (fun (typ, c) (arg, exvar) ->
                               TypeConv.arrow tenv exvar typ,
                               c ^ infer_expr tenv arg exvar
                             )
                             (t, CTrue e.expr_loc)
                             (List.rev exs) in
              c ^ (SName dcid <? typ) e.expr_loc
            )

    | E_record fields ->
        (** Lookup the record ADT matched by this set of fields, and
            constrain each field value to the result type of the
            corresponding field destructor. *)
        let fields = AstUtils.sort_fields fields in
        let f_names, f_vals = List.split fields in
        let rec_info = lookup_record_adt tenv f_names in
        let rcon =
          Printf.sprintf "<%s>" (Location.value rec_info.adt) in
        exists_list f_vals (
            fun exs ->
            let typ, c = List.fold_left
                           (fun (typ, c) (fval, exvar) ->
                             TypeConv.arrow tenv exvar typ,
                             c ^ infer_expr tenv fval exvar
                           )
                           (t, CTrue e.expr_loc)
                           (List.rev exs) in
            c ^ (SName rcon <? typ) e.expr_loc
          )
    | E_field (exp, f) ->
        (** A record field index is similar to a data constructor but
            has no arity check; its constraint makes its destructor
            type equal to the type taking [exp] to [t].*)
        let field = Location.value f in
        let _ = lookup_field_destructor tenv (Location.loc f) (LName field) in
        let binding = Printf.sprintf "{%s}" field in
        exists (fun exvar ->
            let typ = TypeConv.arrow tenv exvar t in
            infer_expr tenv exp exvar
            ^ (SName binding <? typ) e.expr_loc
          )
    | E_apply (fexp, args) ->
        (** The constraint of an [apply] makes equal the type of the
            function expression [fexp] and the function type taking the
            types of arguments [args] to [t]. *)

        (* an empty argument list corresponds to an argument of unit *)
        if List.length args = 0 then
          let unit = typcon_variable tenv (TName "unit") in
          let typ = TypeConv.arrow tenv unit t in
          infer_expr tenv fexp typ
        else
          exists_list args (
              fun exs ->
              let typ, cargs = List.fold_left
                                 (fun (typ, c) (arg, exvar) ->
                                   TypeConv.arrow tenv exvar typ,
                                   c ^ infer_expr tenv arg exvar
                                 )
                                 (t, CTrue e.expr_loc)
                                 (List.rev exs) in
              let cfun = infer_expr tenv fexp typ in
              cfun ^ cargs
            )
    | E_match (exp, typ, dc) ->
        (** Desugar this as a case expression:

            case (exp) { typ::dc _ _ _ => true, _ => false }

            We cannot do it in the parser since we need to know the
            arity of the data constructor [dc] to generate the correct
            wildcard case pattern.  The return type is constrained to
            be boolean. *)
        let dcid, dcloc = Location.value dc, Location.loc dc in
        let arity, _, _ = lookup_datacon tenv dcloc (DName dcid) in
        let case_exp = make_match_case_expr exp typ dc arity e.expr_loc in
        let bool_typ = type_of_primitive (as_fun tenv) (PL_bool true) in
        (infer_expr tenv case_exp t) ^ (t =?= bool_typ) e.expr_loc
    | E_literal prim_lit ->
        (* TODO: support various integer types *)
        let primtyp = type_of_primitive (as_fun tenv) prim_lit in
        (t =?= primtyp) e.expr_loc
    | E_case (exp, clauses) ->
        (** The constraint of a [case] makes equal the type of the
            scrutinee and the type of every branch pattern. The body
            of each branch must be equal to [t]. *)
        (* TODO: exhaustiveness check of patterns *)
        exists (fun exvar ->
            infer_expr tenv exp exvar ^
              conj
                (List.map
                   (fun (p, b) ->
                     let fragment = infer_pat_fragment tenv p exvar in
                     CLet ([ Scheme (p.pattern_loc, [],
                                     fragment.vars,
                                     fragment.tconstraint,
                                     fragment.gamma)
                           ],
                           infer_expr tenv b t))
                   clauses))
    | E_let (p, def, body) ->
        (** The constraint of this non-generalizing [let] makes equal
            the type of the pattern and the definiens, and requires
            the type of the let body to be equal to [t]. *)
        exists (fun exvar ->
            let fragment = infer_pat_fragment tenv p exvar in
            let def_con = infer_expr tenv def exvar in
            def_con
            ^ (ex ?pos:(Some e.expr_loc) fragment.vars
                 (CLet (
                      (* Bind the variables of [p] via a monomorphic
                         [let] constraint. *)
                      [ monoscheme fragment.gamma ],
                      (* Require [exvar] to be a valid type for [p]. *)
                      fragment.tconstraint
                      (* Require [t] to be a valid type for [body]. *)
                      ^ infer_expr tenv body t))
              )
          )
    | E_cast (exp, typ) ->
        (** A type constraint inserts a type equality into the
            generated constraint. *)
        let ityp = TypeConv.intern tenv typ in
        (t =?= ityp) e.expr_loc ^ infer_expr tenv exp ityp
    | E_unop (op, e) ->
        (** This is a special case of a constructor application. *)
        exists (fun exvar ->
            let opid = unop_const_name op in
            let typ = TypeConv.arrow tenv exvar t in
            infer_expr tenv e exvar
            ^ (SName opid <? typ) e.expr_loc
          )
    | E_binop (op, le, re) ->
        exists (fun lexvar ->
            exists (fun rexvar ->
                let opid = binop_const_name op in
                let typ = TypeConv.arrow tenv lexvar
                            (TypeConv.arrow tenv rexvar t) in
                infer_expr tenv le lexvar
                ^ infer_expr tenv re rexvar
                ^ (SName opid <? typ) e.expr_loc
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
        (SName id <? t) loc

(** [infer_fun_defn tenv ctxt fd] examines the function definition [fd]
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

  let irestyp = TypeConv.intern tenv' fd.fun_defn_res_type in
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
          let ityp = TypeConv.intern tenv' typ in
          let v = variable Flexible () in
          acu_ids,
          { gamma = StringMap.add pn (CoreAlgebra.TVariable v, ploc)
                      bindings.gamma;
            tconstraint = (CoreAlgebra.TVariable v =?= ityp) ploc
                          ^ bindings.tconstraint;
            vars = v :: bindings.vars },
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
  let body_c = infer_expr tenv' fd.fun_defn_body irestyp in

  (* Construct the constrained binding for the polymorphic function
     definition itself. *)

  let scheme =
    let def_c = CLet ([arg_schm],
                      (ftyp =?= signature) loc
                      ^ body_c) in
    let bind = StringMap.singleton fdn (ftyp, loc) in
    Scheme (fd.fun_defn_loc, rqs, [fv], def_c, bind) in

  (* Generate the constraint context. *)
  (fun c -> ctxt (CLet ([scheme], c)))


(** [infer_nt_rhs_type tenv ntd] tries to deduce a type for the
    right-hand side of the definition of [ntd]. This is done
    in the following cases:
    . there is a single production with a single non-terminal
      - the inferred type is the type of that non-terminal
    . all the productions are regular expressions
      - the inferred type is a string
    There cannot be any action elements, and any constraint elements
    are ignored.

    TODO: this could be extended, e.g. for the above under a star or option
    operator, or restricted to views, etc.
 *)
let infer_nt_rhs_type tenv ntd =
  let res =
    match ntd.non_term_rules with
      (* a single production with a single non-terminal *)
      | [{ rule_rhs = [{ rule_elem = RE_non_term (n, _) }] }] ->
          lookup_non_term_type tenv (NName (Location.value n))
      (* each production is a sequence of unnamed regular expressions *)
      | rules ->
          let is_regexp =
            List.for_all (fun r ->
                List.for_all (fun re ->
                    match re.rule_elem with
                      | RE_epsilon
                      | RE_regexp _
                      | RE_constraint _ -> true
                      | _ -> false
                  ) r.rule_rhs
              ) rules in
          if is_regexp then
            Some (lookup_type_variable ~pos:ntd.non_term_loc tenv (TName "string"))
          else
            None in
  match res with
    | Some t -> t
    | None ->
        raise (Error (NTTypeNotInferrable ntd.non_term_name))

let infer_non_term_inh_type tenv ntd =
  let nid = ntd.non_term_name in
  List.fold_left (fun ats (pid, te) ->
      let p = Location.value pid in
      let t = TypeConv.intern tenv te in
      match StringMap.find_opt p ats with
        | Some (_, l) ->
            let repid = Location.mk_loc_val p l in
            raise (Error (NTRepeatedBinding (nid, pid, repid)))
        | None ->
            StringMap.add p (t, Location.loc pid) ats
    ) StringMap.empty ntd.non_term_inh_attrs

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
        let tvar = infer_nt_rhs_type tenv ntd in
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
        let tenv', dids, drqs, let_env =
          List.fold_left
            (intern_field_destructor ntid [])
            (tenv', [], [], StringMap.empty)
            attrs in
        let tenv', cid, crqs, let_env =
          intern_record_constructor ntid []
            (tenv', let_env) attrs in
        let fields, _ = List.split attrs in
        let rec_info = { adt = ntid;
                         fields;
                         record_constructor = cid;
                         field_destructors = dids } in
        rcd := Some rec_info;
        adt := Some { adt = Record rec_info;
                      loc };
        let ctxt' = (fun c ->
            ctxt' (CLet ([Scheme (loc, drqs @ crqs, [], CTrue loc, let_env)],
                         c))
          ) in
        tenv', ctxt'

(* returns a constraint ensuring that the non-terminal [id] has a
   string type *)
let rec check_string_non_term tenv id =
  let n = Location.value id in
  let str = typcon_variable tenv (TName "string") in
  match lookup_non_term_type tenv (NName n) with
    | None ->
        raise (Error (UnknownNonTerminal id))
    | Some t ->
        (t =?= str) (Location.loc id)

let rec check_literals tenv ls =
  match ls.literal_set with
    | LS_type id ->
        (* This non-terminal should have string type *)
        check_string_non_term tenv id
    | LS_diff (l, r) ->
        (check_literals tenv l) ^ (check_literals tenv r)
    | LS_set _ | LS_range (_, _) ->
        (* Literals will always have the type string *)
        CTrue ls.literal_set_loc

let rec check_regexp tenv re =
  match re.regexp with
    | RX_literals ls ->
        check_literals tenv ls
    | RX_wildcard ->
        CTrue re.regexp_loc
    | RX_type id ->
        (* This non-terminal should have string type *)
        check_string_non_term tenv id
    | RX_star (re', None) ->
        check_regexp tenv re'
    | RX_star (re', Some e) ->
        let int = typcon_variable tenv (TName "int") in
        (check_regexp tenv re'
         ^ infer_expr tenv e int)
    | RX_opt re' ->
        check_regexp tenv re'
    | RX_choice rels ->
        conj (List.map (check_regexp tenv) rels)
    | RX_seq rels ->
        conj (List.map (check_regexp tenv) rels)

let check_stmt tenv s t =
  match s.stmt with
    | S_expr e ->
        infer_expr tenv e t
    | S_assign (l, r) ->
        let u = typcon_variable tenv (TName "unit") in
        exists (fun t' ->
            (infer_expr tenv l t'
             ^ infer_expr tenv r t'
             ^ (t =?= u) s.stmt_loc))

let infer_action tenv act t =
  (* [t] can only bind the last expression if any of the sequence,
   * otherwise it should equal [unit]. *)
  let rec process_stmts = function
    | [] ->
        CTrue act.action_loc
    | [ s ] ->
        (* [t] applies to the last stmt *)
        check_stmt tenv s t
    | s :: t ->
        (* all non-tail statements must have [unit] type *)
        let u = typcon_variable tenv (TName "unit") in
        let c = check_stmt tenv s u in
        c ^ (process_stmts t)
  in process_stmts act.action_stmts

let rec infer_rule_elem tenv ntd ctx re t =
  let pack_constraint c' =
    (fun c -> ctx (c' ^ c)) in
  match re.rule_elem with
    | RE_regexp r ->
        (* regular expressions have string types *)
        let s = typcon_variable tenv (TName "string") in
        let c = ((t =?= s) re.rule_elem_loc
                 ^ check_regexp tenv r) in
        pack_constraint c
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
                      pack_constraint c
                  | Some (id, _) ->
                      raise (Error (NTInheritedUnspecified (nid, id))))
        )
    | RE_non_term (cntid, Some attrvals) ->
        let cntn = Location.value cntid in
        let cnti = match lookup_non_term tenv (NName cntn) with
            | None -> raise (Error (UnknownNonTerminal cntid))
            | Some (inh_typ, _) -> inh_typ in
        let pids, cnstrs =
          List.fold_left (fun (pids, cnstrs) (pid, e) ->
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
              let cnstr = infer_expr tenv e typ in
              pids, cnstr :: cnstrs
            ) (StringMap.empty, []) attrvals in
        StringMap.iter (fun pn _ ->
            if not (StringMap.mem pn pids)
            then raise (Error (NTInheritedUnspecified (cntid, pn)))
          ) cnti;
        let c = conj cnstrs in
        pack_constraint c
    | RE_constraint rc ->
        let b = typcon_variable tenv (TName "bool") in
        let c = ((t =?= b) re.rule_elem_loc
                 ^ infer_expr tenv rc b) in
        pack_constraint c
    | RE_action a ->
        pack_constraint (infer_action tenv a t)
    | RE_named (id, re') ->
        (* [id] is bound in the environment when typing [re'] *)
        let idloc = Location.loc id in
        let id    = Location.value id in
        let ctx'  = infer_rule_elem tenv ntd (fun c -> c) re' t in
        (fun c ->
          ctx (CLet ([Scheme (re.rule_elem_loc, [], [],
                              CTrue re.rule_elem_loc,
                              StringMap.singleton id (t, idloc))],
                     ctx' c)))
    | RE_seq rels ->
        (* A sequence has a tuple type formed from the individual
           rule elements *)
        (fun c ->
          ctx (exists_list rels (fun assoc ->
                   let ctx' =
                     List.fold_left (fun ctx' (re', t') ->
                         infer_rule_elem tenv ntd ctx' re' t'
                       ) (fun c -> c) assoc in
                   let qs = snd (List.split assoc) in
                   let tup = tuple (typcon_variable tenv) qs in
                   ((t =?= tup) re.rule_elem_loc
                    ^ ctx' c)))
        )
    | RE_choice rels ->
        (* Each choice should have the same type [t]. *)
        let ctx' = List.fold_left (fun ctx re ->
                       infer_rule_elem tenv ntd ctx re t
                     ) (fun c -> c) rels in
        (fun c -> ctx (ctx' c))
    | RE_star (re', None) ->
        (* [re] has a type [list t'] where [t'] is the type of [re'] *)
        (fun c ->
          ctx (exists (fun t' ->
                   let ctx' =
                     infer_rule_elem tenv ntd (fun c -> c) re' t' in
                   let lst = list (typcon_variable tenv) t' in
                   (ctx' c
                    ^ (t =?= lst) re.rule_elem_loc))))
    | RE_star (re', Some e) ->
        (* [re] has a type [list t'] where [t'] is the type of [re']
           and [e] has type int *)
        let int = typcon_variable tenv (TName "int") in
        (fun c ->
          ctx (exists (fun t' ->
                   let ctx' =
                     infer_rule_elem tenv ntd (fun c -> c) re' t' in
                   let lst = list (typcon_variable tenv) t' in

                   (ctx' c
                    ^ (t =?= lst) re.rule_elem_loc
                    ^ infer_expr tenv e int))))
    | RE_opt re' ->
        (* [re] has a type [option t'] where [t'] is the type of [re'] *)
        (fun c ->
          ctx (exists (fun t' ->
                   let ctx' =
                     infer_rule_elem tenv ntd (fun c -> c) re' t' in
                   let opt = option (typcon_variable tenv) t' in
                   (ctx' c
                    ^ (t =?= opt) re.rule_elem_loc))))
    | RE_epsilon ->
        let u = typcon_variable tenv (TName "unit") in
        let c = (t =?= u) re.rule_elem_loc in
        pack_constraint c
    | RE_at_pos (e, re') ->
        (* [pos] needs to be an integer and [re'] should have type [t] *)
        let int = typcon_variable tenv (TName "int") in
        let ctx' = infer_rule_elem tenv ntd (fun c -> c) re' t in
        (fun c -> ctx (ctx' c
                       ^ infer_expr tenv e int))
    | RE_at_buf (buf, re') ->
        (* [buf] should have type [view] and [re'] should have type [t] *)
        let view = typcon_variable tenv (TName "view") in
        let ctx' = infer_rule_elem tenv ntd (fun c -> c) re' t in
        (fun c -> ctx (ctx' c
                       ^ infer_expr tenv buf view))
    | RE_map_bufs (bufs, re') ->
        (* [bufs] should have type [list view] and [re] should have
         * type [list t'] where [t'] is the type of [re'] *)
        let view = typcon_variable tenv (TName "view") in
        let views = list (typcon_variable tenv) view in
        (fun c ->
          ctx (exists (fun t' ->
                   let ctx' =
                     infer_rule_elem tenv ntd (fun c -> c) re' t' in
                   let result = list (typcon_variable tenv) t' in
                   (ctx' c
                    ^ infer_expr tenv bufs views
                    ^ (t =?= result) re.rule_elem_loc))))

let infer_non_term_rule tenv ntd rule pids =
  (* add temporaries to local bindings *)
  let pids, bindings =
    List.fold_left (fun (pids, fragment) (pid, typ) ->
        let pn, ploc = Location.value pid, Location.loc pid in
        let pids =
          match StringMap.find_opt pn pids with
            | Some repid ->
                raise (Error (NTRepeatedBinding (ntd.non_term_name, pid, repid)))
            | None ->
                StringMap.add pn pid pids in
        let ityp = TypeConv.intern tenv typ in
        let v = variable Flexible () in
        pids,
        { gamma = StringMap.add pn (CoreAlgebra.TVariable v, ploc)
                    fragment.gamma;
          tconstraint = (CoreAlgebra.TVariable v =?= ityp) ploc
                        ^ fragment.tconstraint;
          vars = v :: fragment.vars }
      ) (pids, empty_fragment) rule.rule_temps in
  let qs, ctx = List.fold_left (fun (qs, ctx) re ->
                    let v = variable Flexible () in
                    (v :: qs,
                     infer_rule_elem tenv ntd ctx re (CoreAlgebra.TVariable v))
                  ) ([], (fun c -> c)) rule.rule_rhs in
  CLet ([ Scheme (rule.rule_loc, [],
                  bindings.vars @ qs,
                  bindings.tconstraint ^ (ctx (CTrue rule.rule_loc)),
                  bindings.gamma) ],
        CTrue rule.rule_loc)

let infer_non_term tenv ntd =
  let ntid = NName (Location.value ntd.non_term_name) in
  let inh_attrs = match lookup_non_term tenv ntid with
      | None ->
          (* the type definition is processed in the previous typing
             pass and should already be present *)
          assert false
      | Some (i, _) -> i in

  (* compute the local bindings for each rule *)
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
          { gamma = StringMap.singleton (Location.value n)
                      (CoreAlgebra.TVariable v, nloc);
            tconstraint = (CoreAlgebra.TVariable v =?= ntt) nloc;
            vars = [ v ] } in
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
        { gamma = StringMap.add pn (CoreAlgebra.TVariable v, ploc)
                    fragment.gamma;
          tconstraint = (CoreAlgebra.TVariable v =?= ityp) ploc
                        ^ fragment.tconstraint;
          vars = v :: fragment.vars }
      ) (pids, bindings) (StringMap.bindings inh_attrs) in
  conj
    (List.map
       (fun r ->
         CLet ([ Scheme (r.rule_loc, [],
                         bindings.vars,
                         bindings.tconstraint,
                         bindings.gamma) ],
               infer_non_term_rule tenv ntd r pids))
       ntd.non_term_rules)

(** Initialize the typing environment with the builtin types and
    constants. *)
let init_tenv () =
  let builtin_types =
    init_builtin_types (fun ?name () -> variable Rigid ?name:name ()) in

  (* Add the builtin data constructors into the environment.  The
     builtins currently only use variant algebraic types. *)
  let init_ds (TName adt_name) env_info ds =
    let adt_id = Location.mk_ghost adt_name in
    let (tenv, dcs, lrqs, let_env) as env_info =
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
  let (init_tenv, acu, lrqs, let_env) =
    List.fold_left
      (fun (tenv, dvs, lrqs, let_env) (n, (kind, v, ds)) ->
        let r = ref None in
        let tenv = add_type_constructor tenv Location.ghost_loc n
                     (KindInferencer.intern_kind (as_kind_env tenv) kind,
                      variable ~name:n Constant (),
                      r) in
        let (dcs, env_info) =
          init_ds n (tenv, dvs, lrqs, let_env) ds in
        (* If there are no data constructors, it does not need
           any adt_info. *)
        if List.length dcs > 0
        then r := Some { adt = Variant dcs;
                         loc = Location.ghost_loc };
        env_info
      )
      (empty_environment, [], [], StringMap.empty)
      (List.rev builtin_types)
  in
  (* Extract the variables bound to the type constructors. *)
  let vs =
    fold_type_info (fun vs (n, (_, v, _)) -> v :: vs) [] init_tenv
  in

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

  (* The initial environment is implemented as a constraint
     context. *)
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

let infer_spec tenv spec =
  (* First pass: process the expression language, and the
     type-definitions for the non-terminals *)
  let tenv, ctxt =
    List.fold_left (fun (tenv, ctxt) decl ->
        match decl with
          | Decl_types tds ->
              (* TODO: handle recursive declarations *)
              List.fold_left (fun (te, c) td ->
                  infer_type_decl te c td
                ) (tenv, ctxt) tds
          | Decl_fun f ->
              (* TODO: solve eagerly? *)
              let c = infer_fun_defn tenv ctxt f in
              tenv, c
          | Decl_format f ->
              List.fold_left (fun (te, c) fd ->
                  let ntd = fd.format_decl in
                  infer_non_term_type te c ntd
                ) (tenv, ctxt) f.format_decls
          | _ ->
              tenv, ctxt
      ) (tenv, (fun c -> c)) spec.decls in

  (* Second pass: process the grammar spec comprising the rules for
     each non-terminal. *)
  let cnstr =
    List.fold_left (fun cnstr decl ->
        match decl with
          | Decl_format f ->
              List.fold_left (fun c fd ->
                  let ntd = fd.format_decl in
                  let cnstr = infer_non_term tenv ntd in
                  c ^ cnstr
                ) cnstr f.format_decls
          | _ ->
              cnstr
      ) (CTrue Location.ghost_loc) spec.decls in

  let ctxt = (fun c -> ctxt (c ^ cnstr)) in
  tenv, ctxt

let generate_constraint spec =
  let tenv, c = init_tenv () in
  c ((snd (infer_spec tenv spec)) (CDump Location.ghost_loc))
