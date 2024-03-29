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

(** This module implements type inference and checking. *)

open Parsing
open TypeConstraint
open TypeAlgebra
open MultiEquation
open TypingEnvironment
open TypingExceptions
open Ast

module StringSet = Set.Make(String)
module StringMap = Misc.StringMap

(** Local variable naming environment.

    This is used to annotate variables with unique binding
    identifiers (integers). *)

(* binding identifier *)
type varid = int
let varid_to_string = string_of_int

module VEnv : sig
  type t

  val empty:     t

  (* update current module *)
  val in_module: t -> string -> t
  (* retrieve current module *)
  val cur_module: t -> string

  val add:       t -> unit var -> varid var * t
  val extend:    t -> string -> varid var -> t
  val lookup:    t -> unit var -> varid var option

  val fold_left: ('a -> varid var -> 'a) -> 'a -> t -> 'a
end = struct
  (* Binding entries are tagged with the current module when created; on
     lookup, the current module is compared to the binding entry's
     module to ensure that the lookup in within module scope. *)
  type modul = string
  type t = (modul * string, varid var) CoreEnv.t * modul

  let binding = ref (-1)

  let empty = CoreEnv.empty, ""

  let in_module (env, _) m = (env, m)
  let cur_module (_, m) = m

  let add (env, m) v =
    incr binding;
    let l = Location.loc v in
    let n = var_name v in
    let v = Location.mk_loc_val (n, !binding) l in
    v, (CoreEnv.add env (m, n) v, m)

  let extend (env, m) n v =
    CoreEnv.add env (m, n) v, m

  let lookup (env, m) v =
    CoreEnv.lookup_opt env (m, var_name v)

  let fold_left f a (t, _) =
    CoreEnv.fold_left (fun a (_, v) -> f a v) a t
end

let ident_of_var v =
  Location.mk_loc_val (var_name v) (Location.loc v)

let stdlib = AstUtils.stdlib
let infer_mod = AstUtils.infer_mod

let std_type (t: string) =
  stdlib, TName t

let std_tname (t: tname) =
  stdlib, t

(** Check a literal type and bounds. *)

let check_literal lit loc =
  match lit with
    | PL_int (i, nt) ->
        if   not (AstUtils.check_int_literal nt i)
        then let err = Invalid_integer_value (i, nt) in
             raise (Error (loc, err))
    | _ -> ()

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
      with StringMap.Strict x -> raise (Error (pos, NonLinearPattern x)));
   vars        = f1.vars @ f2.vars;
   tconstraint = f1.tconstraint ^ f2.tconstraint}

(** [infer_pat_fragment tenv venv p t] generates a fragment that represents the
    information gained by a success when matching p, and an updated variable
    binding environment from [venv] *)
let infer_pat_fragment tenv (venv: VEnv.t) (p: (unit, unit, mod_qual) pattern) (t: crterm)
    : fragment * (crterm, varid, mod_qual) pattern * VEnv.t =
  let join pos = List.fold_left (join_fragment pos) empty_fragment in
  let rec infpat t p venv =
    let mk_auxpat p' =
      {pattern = p'; pattern_loc = p.pattern_loc; pattern_aux = t} in
    let pos = p.pattern_loc in
    match p.pattern with
      (* Wildcard pattern does not generate any fragment. *)
      | P_wildcard ->
          empty_fragment, mk_auxpat P_wildcard, venv

      (* We refer to the algebra to know the type of a primitive. *)
      | P_literal l ->
          {empty_fragment with
            tconstraint = (t =?= type_of_primitive (as_fun tenv) l) pos},
          mk_auxpat (P_literal l),
          venv

      (* Matching against a variable generates a fresh flexible
         variable, binds it to the [name] and forces the variable to
         be equal to [t].
         The binding environment is updated, and an annotated binding
         is generated for the pattern variable.*)
      | P_var name ->
          let pos = Location.loc name in
          let v = variable Flexible () in
          let v', venv' = VEnv.add venv name in
          {gamma       = StringMap.singleton
                           (var_name name)
                           (CoreAlgebra.TVariable v, pos);
           tconstraint = (CoreAlgebra.TVariable v =?= t) pos;
           vars        = [ v ]},
          mk_auxpat (P_var v'),
          venv'

      (* Matching against a data constructor generates the fragment
         that:
         - forces [t] to be the type of the constructed value
         - constraints the types of the subpatterns to be equal to the
           arguments of the data constructor. *)
      | P_variant ((m, typ, c), ps) ->
          let typid = Location.value typ in
          let cid, cloc = Location.value c, Location.loc c in
          let dcid = AstUtils.canonicalize_dcon typid cid in
          let alphas, ct = fresh_datacon_scheme tenv cloc (m, (DName dcid)) in
          let rt = result_type (as_fun tenv) ct
          and ats = arg_types (as_fun tenv) ct in
          if   List.length ps <> List.length ats
          then let nexp = List.length ats in
               let ngot = List.length ps in
               let err  = InvalidPatternArgs (c, nexp, ngot) in
               raise (Error (pos, err))
          else let fs, ps', venv' =
                 List.fold_left
                   (fun (fs, ps', venv) (at, p) ->
                     let f, p', venv' = infpat at p venv in
                     f :: fs, p' :: ps', venv')
                   ([], [], venv)
                   (List.combine ats ps) in
               let fragment = join pos (List.rev fs) in
               {fragment with
                 tconstraint = fragment.tconstraint ^ (t =?= rt) pos;
                 vars        = alphas @ fragment.vars},
               mk_auxpat (P_variant ((m, typ, c), List.rev ps')),
               venv'
  (* TODO: add record patterns *) in
  infpat t p venv

(** checks for consistency between the declarations and
    uses of type variables *)
let check_distinct_tvars _typid qs =
  let rec checker acc = function
    | [] -> None
    | var :: tl ->
        let v = Location.value var in
        if   StringSet.mem v acc
        then Some var
        else checker (StringSet.add v acc) tl in
  match checker StringSet.empty qs with
    | Some var -> raise (Error (Location.loc var, DuplicateTypeVariable var))
    | None     -> ()

let check_tvars_usage tenv m _t qs used_set =
  (* make sure all declared type variables are used *)
  let decl_vs =
    List.fold_left (fun acc q ->
        let v = Location.value q in
        if   not (StringMap.mem v used_set)
        then raise (Error (Location.loc q, UnusedTypeVariable q))
        else StringSet.add v acc
      ) StringSet.empty qs in
  (* make sure all used vars are declared or defined *)
  StringMap.iter (fun v loc ->
      if   not (StringSet.mem v decl_vs || is_defined_type tenv (m, TName v))
      then raise (Error (loc, UnboundTypeIdentifier (std_tname (TName v))))
    ) used_set

(** [make_dc_signature adt tvars dc typ] constructs the function type
    signature for a data constructor of [adt] named [dc] given its declared
    argument [typ], which is parameterized over type variables [tvars]. *)
let make_dc_signature (m: mname) (adt: ident) tvars _dc typ
  : type_expr =
  let tvars = List.map AstUtils.make_tvar tvars in
  let res =
    if   List.length tvars = 0
    then AstUtils.make_tname_id m adt
    else AstUtils.make_mod_type_app m
           (Location.value adt) tvars (Location.loc adt) in
  match typ with
    | None      -> res
    | Some sign -> AstUtils.add_arrow_result sign res

(** name of the field destructor in the typing constraint *)
let constr_name_data_constructor (m: mname) (t: ident) (d: ident) =
  Printf.sprintf "%s%s::%s"
    (AstUtils.mk_modprefix m) (Location.value t) (Location.value d)

(** [intern_data_constructor external adt_ident env_info dcon_info] returns
    env_info augmented with the data constructor's typing information
    It also checks if its definition is legal. [internal] specifies
    whether this is a builtin or from an external spec. *)
let intern_data_constructor internal (m: mname) adt_id qs env_info dcon_info =
  let adt_name = Location.value adt_id in
  let tenv, acu, lrqs, let_env = env_info
  and dname, opt_arg = dcon_info in
  let typ =
    (* Internal builtins have full signatures, whereas parsed
       signatures leave the result type implicit.  This shows up in
       constant data constructors, where make_dc_signature would
       otherwise add an unnecessary return type. *)
    if   internal
    then Misc.unSome opt_arg
    else make_dc_signature m adt_id qs dname opt_arg in
  let qs = List.map (fun q -> stdlib, TName (Location.value q)) qs in
  let rqs, rtenv = fresh_unnamed_rigid_vars (Location.loc adt_id) tenv qs in
  let tenv' = add_type_variables rtenv tenv in
  let ityp = TypeConv.intern tenv' typ in
  let _ =
    if   not (is_regular_datacon_scheme tenv (m, TName adt_name) rqs ityp)
    then let l = Location.loc dname in
         raise (Error (l, InvalidDataConstructorDefinition dname)) in
  let pos = Location.loc dname in
  let binding = constr_name_data_constructor m adt_id dname in
  let dname = Location.value dname in
  let dcid = AstUtils.canonicalize_dcon adt_name dname in
  let v = variable ~structure:ityp Flexible () in
  ((add_data_constructor tenv pos (m, TName adt_name) (DName dcid)
      (TypeConv.arity typ, rqs, ityp)),
   (DName dname, v) :: acu,
   (rqs @ lrqs),
   StringMap.add binding (ityp, pos) let_env)

(** [make_field_signature adt tvars f typ] constructs the field type
    and the function type signature for a destructor of [adt] named
    [f] given its declared argument [typ], which is parameterized over
    type variables [tvars]. *)
let make_field_signature (m: mname) (adt: ident) tvars f typ =
  let tvars = List.map AstUtils.make_tvar tvars in
  let source =
    if   List.length tvars = 0
    then AstUtils.make_tname_id m adt
    else AstUtils.make_mod_type_app m
           (Location.value adt) tvars (Location.loc adt) in
  (* TODO: we forbid function types as field types.  Currently, this
     is by enforced by construction at the syntax level, but we should
     also check it here, e.g. for builtins. *)
  AstUtils.make_arrow_type [source; typ] (Location.loc f)

(** name of the field destructor in the typing constraint *)
let constr_name_field_destructor (m: mname) (f: ident) =
  Printf.sprintf "{%s%s}" (AstUtils.mk_modprefix m) (Location.value f)

(** [intern_field_destructor adt_name env_info f_info] returns
    env_info augmented with the field destructor's typing information
    It also checks if its definition is legal. *)
let intern_field_destructor m adt_id qs env_info f_info =
  let adt_name = Location.value adt_id in
  let tenv, acu, lrqs, let_env = env_info
  and fname, typ = f_info in
  let destructor = make_field_signature m adt_id qs fname typ in
  let qs = List.map (fun q -> stdlib, TName (Location.value q)) qs in
  let rqs, rtenv = fresh_unnamed_rigid_vars (Location.loc adt_id) tenv qs in
  let tenv' = add_type_variables rtenv tenv in
  let ityp = TypeConv.intern tenv' destructor in
  (if   not (is_regular_field_scheme tenv (m, TName adt_name) rqs ityp)
   then let l = Location.loc fname in
        raise (Error (l, InvalidFieldDestructorDefinition fname)));
  let pos = Location.loc fname in
  let binding = constr_name_field_destructor m fname in
  let fname = Location.value fname in
  let v = variable ~structure:ityp Flexible () in
  ((add_field_destructor tenv pos (m, TName adt_name) (m, LName fname)
      (rqs, ityp)),
   (LName fname, v) :: acu,
   (rqs @ lrqs),
   StringMap.add binding (ityp, pos) let_env)

(* The constructor is the function with argument types from the fields
   in increasing order, and with the record as the result type. *)
let make_record_signature (m: mname) (adt: ident) tvars fields =
  let tvars = List.map AstUtils.make_tvar tvars in
  let res =
    if   List.length tvars = 0
    then AstUtils.make_tname_id m adt
    else AstUtils.make_mod_type_app m
           (Location.value adt) tvars (Location.loc adt) in
  let fields = AstUtils.sort_fields (List.map (fun (f, e) -> (m, f), e) fields) in
  let signature =
    List.fold_left (fun acc ((_m, f), t) ->
        AstUtils.make_arrow_type [t; acc] (Location.loc f)
      ) res (List.rev fields) in
    signature, fields

(** name of the record constructor in the typing constraint *)
let constr_name_record_constructor (m: mname) (adt_id: ident) =
  Printf.sprintf "<%s%s>" (AstUtils.mk_modprefix m) (Location.value adt_id)

(** [intern_record_constructor adt_name env_info fields] returns
    env_info augmented with the record constructor's typing
    information.  The constructor is named '<adt>' for a record named
    'adt'. *)
let intern_record_constructor (m: mname) (adt_id: ident) qs env_info fields =
  let adt_name = Location.value adt_id in
  let tenv, let_env = env_info in
  let rcon = constr_name_record_constructor m adt_id in
  let constructor, _fields = make_record_signature m adt_id qs fields in
  let qs = List.map (fun q -> stdlib, TName (Location.value q)) qs in
  let rqs, rtenv = fresh_unnamed_rigid_vars (Location.loc adt_id) tenv qs in
  let tenv' = add_type_variables rtenv tenv in
  let ityp = TypeConv.intern tenv' constructor in
  let pos = Location.loc adt_id in
  let v = variable ~structure:ityp Flexible () in
  ((add_record_constructor tenv (m, TName adt_name) (rqs, ityp)),
   (TName rcon, v),
   rqs,
   StringMap.add rcon (ityp, pos) let_env)

(** [check_valid_type_defn t qs defn] checks whether [defn] is a valid type
    definition for the declared quantified type variables [qs]. *)
let check_valid_type_defn tenv m t qs defn =
  check_tvars_usage tenv m t qs (TypeConv.variables_of_typ defn)

(** [check_fields bf fields] ensures that the bit index ranges of
   the [fields] of a bitfield [bf] cover the entire corresponding
   bitvector, and do not overlap.  It returns the length of the
   bitvector. *)
let check_fields bf fields : int =
  let rec check_ranges = function
    | [] -> ()
    | (_, (n, m)) :: rest ->
        let n', m' = Location.value n, Location.value m in
        let nl, ml = Location.loc n, Location.loc m in
        let ext = Location.extent nl ml in
        if   m' < 0
        then let err = InvalidBitrangeLowBound m' in
             raise (Error (ml, err))
        else if n' < m'
        then let err = InvalidBitrangeOrder (n', m') in
             raise (Error (ext, err))
        else check_ranges rest in
  check_ranges fields;
  let fields =
    List.sort (fun (_, r) (_, r') -> compare r r') fields in
  let first = ref true in
  let rec check_cover = function
    | [] ->
        assert false
    | (_, (x, n)) :: [] ->
        (if   !first && Location.value n != 0
         then let err = IncompleteBitfieldRanges (bf, 0) in
              raise (Error (Location.loc bf, err)));
        1 + Location.value x
    | (f, (x, n)) :: ((f', (_, n')) :: _ as rest) ->
        (if   !first && Location.value n != 0
         then let err = IncompleteBitfieldRanges (bf, 0) in
              raise (Error (Location.loc bf, err)));
        first := false;
        let x, n' = Location.value x, Location.value n' in
        if   x >= n'
        then let err = OverlappingBitfieldRanges (bf, f, f', n') in
             raise (Error (Location.loc bf, err))
        else if n' > x + 1
        then let err = IncompleteBitfieldRanges (bf, x + 1) in
             raise (Error (Location.loc bf, err))
        else check_cover rest in
  check_cover fields

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
   reference for that constructor collected above. *)

let rec infer_type_decls tenv ctxt tdsloc tds =
  let tenv', tdsrefs, vs =
    List.fold_left (fun (tenv, tdsrefs, vs) td ->
        let name  = Location.value td.type_decl_ident in
        let loc   = td.type_decl_loc in
        let kind  = td.type_decl_kind in
        let kenv  = as_kind_env tenv in
        let mname = infer_mod td.type_decl_mod in
        let k     = KindInferencer.intern_kind kenv kind in
        let v     = variable ~name:(mname, TName name) Constant () in
        let adt   = ref None in
        let tenv' =
          add_type_constructor tenv loc (mname, TName name) (k, v, adt) in
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
                   c)))) in
  tenv, ctxt

(* Perform the second step of type declaration processing: the body of
   each type declaration is processed and added to the environment
   created in the first step.  This step collects the variables and
   bindings needed for the final constraint context for the recursive
   definitions. *)
and infer_type_decl (tenv, rqs, let_env) td adt_ref =
  let ident = td.type_decl_ident
  and loc   = td.type_decl_loc
  and m     = infer_mod td.type_decl_mod
  and tvars = td.type_decl_tvars
  and typ   = td.type_decl_body in
  let process_record_fields fields =
    (* Add the record and field signatures into the environment. *)
    let tenv, dids, drqs, let_env =
      List.fold_left
        (intern_field_destructor m ident tvars)
        (tenv, [], rqs, let_env)
        fields in
    (dids, drqs, intern_record_constructor
                   m ident tvars (tenv, let_env) fields) in
  check_distinct_tvars ident tvars;
  match typ.type_rep with
    | TR_variant dcons ->
        (* First expand any type abbreviations in the signatures. *)
        let dcons =
          List.map (function
              | d, None ->
                  d, None
              | d, Some te ->
                  d, Some (TypedAstUtils.expand_type_abbrevs tenv te)
            ) dcons in
        (* Add the constructor signatures to the environment. *)
        let tenv, ids, rqs, let_env =
          List.fold_left
            (* [false] indicates this is user-specified. *)
            (intern_data_constructor false m ident tvars)
            (tenv, [], rqs, let_env)
            dcons in
        (* Fill in the adt_info. *)
        adt_ref := Some {adt = Variant ids; loc};
        tenv, rqs, let_env
    | TR_record fields ->
        (* First expand any type abbreviations in the signatures. *)
        let fields =
          List.map (fun (f, te) ->
              f, TypedAstUtils.expand_type_abbrevs tenv te
            ) fields in
        let dids, drqs, (tenv, cid, crqs, let_env) =
          process_record_fields fields in
        (* Fill in the adt_info. *)
        adt_ref := Some {adt = Record {adt                = ident;
                                       modul              = m;
                                       fields;
                                       record_constructor = cid;
                                       field_destructors  = dids;
                                       bitfield_info      = None};
                         loc};
        tenv, crqs @ drqs, let_env
    | TR_bitfield fields ->
        let len = check_fields ident fields in
        let fields =
          List.map (fun (f, (hi, lo)) ->
              let hi, lo = Location.value hi, Location.value lo in
              assert (hi >= lo);
              let loc = Location.loc f in
              (f, (AstUtils.make_bitvector_type (1 + hi - lo) loc)),
              (Location.value f, (hi, lo))
            ) fields in
        let fields, finfos = List.split fields in
        let dids, drqs, (tenv, cid, crqs, let_env) =
          process_record_fields fields in
        (* Sort the fields into increasing index order. *)
        let finfos =
          List.sort (fun (_, (l, _)) (_, (r, _)) -> compare l r) finfos in
        (* Fill in the adt_info *)
        let bf_info = {bf_name   = Location.value ident;
                       bf_fields = finfos;
                       bf_length = len} in
        adt_ref := Some {adt = Record {adt                = ident;
                                       modul              = m;
                                       fields;
                                       record_constructor = cid;
                                       field_destructors  = dids;
                                       bitfield_info      = Some bf_info};
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
  let m     = infer_mod td.type_decl_mod in
  match typ.type_rep with
    | TR_defn d ->
        (* First expand any type abbreviations in this abbreviation. *)
        let d' = TypedAstUtils.expand_type_abbrevs tenv d in
        (* Check validity of the resulting type expression. *)
        check_valid_type_defn tenv m ident tvars d';
        (* Add it to the environment *)
        let tvs =
          List.map (fun tv -> TName (Location.value tv)) tvars in
        let abb = {type_abbrev_tvars = tvs;
                   type_abbrev_type  = d'} in
        add_type_abbrev tenv pos (m, TName name) abb
    (* non-abbreviations are handled seperately via checks in infer_spec. *)
    | _ ->
        assert false

let make_match_case_expr m exp typ dcon arity loc =
  let wc = AstUtils.make_pattern_loc P_wildcard loc in
  let bool = Location.mk_loc_val "bool" loc in
  let mk_bool s =
    let v = E_constr ((stdlib, bool, Location.mk_loc_val s loc), []) in
    AstUtils.make_expr_loc v loc in
  let rec mk_pats pats cnt =
    if cnt = 0 then pats else mk_pats (wc::pats) (cnt - 1) in
  let pargs = mk_pats [] arity in
  let pvar = P_variant ((m, typ, dcon), pargs) in
  let pattern = AstUtils.make_pattern_loc pvar loc in
  let tr, fl = mk_bool "True", mk_bool "False" in
  let case_exp = E_case (exp, [pattern, tr; wc, fl]) in
  {expr = case_exp; expr_loc = loc; expr_aux = ()}

(** looks up the adt in [tenv] matching the [fields] in a literal
    record expression; it reports mismatch errors at location [loc]. *)
let lookup_record_adt tenv fields =
  let mid, fid = List.hd fields in (* nonempty list is ensured in the parser *)
  let f = Location.value fid in
  let l = LName f in
  let adtid = match lookup_field_adt tenv (mid, l) with
      | Some adtid ->
          adtid
      | None ->
          raise (Error (Location.loc fid, UnboundRecordField (mid, l))) in
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
  let adt_ident = let _, TName id = adtid in
                  Location.mk_loc_val id rec_loc in
  (* Make sure the used fields match the declared fields. *)
  let decset = List.fold_left (fun acc (field, _) ->
                   let f = Location.value field in
                   (* there should be no duplicates *)
                   assert (not (StringSet.mem f acc));
                   StringSet.add f acc
                 ) StringSet.empty rec_info.fields in
  let useset = List.fold_left (fun acc (mid', fid') ->
                   let f = Location.value fid' in
                   let l' = LName f in
                   let loc = Location.loc fid' in
                   if      AstUtils.mod_compare mid mid' != 0
                   then    let err =
                             InconsistentFieldModules ((mid, l), (mid', l')) in
                           raise (Error (loc, err))
                   else if not (StringSet.mem f decset)
                   then    raise (Error (loc, InvalidRecordField (fid', adt_ident)))
                   else if StringSet.mem f acc
                   then    raise (Error (Location.loc fid', RepeatedRecordField fid'))
                   else StringSet.add f acc
                 ) StringSet.empty fields in
  (match StringSet.choose_opt (StringSet.diff decset useset) with
     | Some f -> let loc = Location.loc adt_ident in
                 raise (Error (loc, IncompleteRecord (adt_ident, f)))
     | None   -> ());
  rec_info

(* In the top-level code for non-terminals and functions (and hence
   their embedded expressions), we need to expand type abbreviations
   in type expressions before interning any types. *)
let intern_expanded_type tenv typ =
  let typ  = TypedAstUtils.expand_type_abbrevs tenv typ in
  TypeConv.intern tenv typ

(* name of the module-qualified value in the typing constraint *)
let constr_name_mod_value (m: mname) v =
  Printf.sprintf "%s%s"
    (AstUtils.mk_modprefix m) (var_name v)

(* Foreign functions are inaccessible outside their defining module. *)
let check_accessible loc tenv (m, v) cur_m =
  let _, foreign = lookup_value loc tenv (m, v) in
  let is_accessible = if   not foreign
                      then true
                      else match m with
                             | Modul Mod_stdlib ->
                                 (* stdlib values should never be foreign *)
                                 assert false
                             | Modul (Mod_inferred m) ->
                                 m = cur_m
                             | Modul (Mod_explicit m) ->
                                 Location.value m = cur_m in
  if   not is_accessible
  then raise (Error (loc, UnknownModItem (m, v)))

(** [infer_expr tenv venv e t] generates a constraint that guarantees that
    [e] has type [t] in the typing environment [tenv]. *)
let rec infer_expr tenv (venv: VEnv.t) (e: (unit, unit, mod_qual) expr) (t : crterm)
        : tconstraint * (width_constraint * (crterm, varid, mod_qual) expr) =
  let mk_auxexpr e' =
    {expr = e'; expr_loc = e.expr_loc; expr_aux = t} in
  match e.expr with
    | E_var v ->
        let v' = match VEnv.lookup venv v with
            | None ->
                let err = UnboundIdentifier (var_name v) in
                raise (Error (e.expr_loc, err))
            | Some v' -> v' in
        (* The type of a variable must be at least as general as [t]. *)
        (SName (var_name v) <? t) (Location.loc v),
        (WC_true,
        mk_auxexpr (E_var v'))
    | E_constr ((m, adt, dcon), args) ->
        (* A data constructor application is similar to the usual
           application except that it must be fully applied. *)
        let dcid = AstUtils.canonicalize_dcon
                     (Location.value adt) (Location.value dcon) in
        let binding = constr_name_data_constructor m adt dcon in
        let cloc = Location.loc dcon in
        let arity, _, _ = lookup_datacon tenv cloc (m, DName dcid) in
        let nargs = List.length args in
        if   nargs <> arity
        then let loc = Location.loc dcon in
             raise (Error (loc, PartialDataConstructorApplication (dcon, arity, nargs)))
        else exists_list_aux args (
                 fun exs ->
                 let typ, c, wc, args =
                   List.fold_left
                     (fun (typ, c, wc, args) (arg, exvar) ->
                       let c', (wc', arg') = infer_expr tenv venv arg exvar in
                       TypeConv.arrow tenv exvar typ,
                       c ^ c',
                       wc @^ wc',
                       arg' :: args)
                     (t, CTrue e.expr_loc, WC_true, [])
                     (List.rev exs) in
                 c ^ (SName binding <? typ) e.expr_loc,
                 (wc,
                  mk_auxexpr (E_constr ((m, adt, dcon), args))))

    | E_record fields ->
        assert (List.length fields > 0);
        (* Lookup the record ADT matched by this set of fields, and
           constrain each field value to the result type of the
           corresponding field destructor. *)
        let fields = AstUtils.sort_fields fields in
        let f_names, _ = List.split fields in
        let rec_info = lookup_record_adt tenv f_names in
        let m = fst (List.hd f_names) in
        let rcon = constr_name_record_constructor m rec_info.adt in
        exists_list_aux fields (
            fun exs ->
            let typ, c, wc, fields =
              List.fold_left
                (fun (typ, c, wc, fields) ((fn, fv), exvar) ->
                  let c', (wc', fv') = infer_expr tenv venv fv exvar in
                  TypeConv.arrow tenv exvar typ,
                  c ^ c',
                  wc @^ wc',
                  (fn, fv') :: fields)
                (t, CTrue e.expr_loc, WC_true, [])
                (List.rev exs) in
            c ^ (SName rcon <? typ) e.expr_loc,
            (wc,
             (* annotated ast has fields in canonical order *)
             mk_auxexpr (E_record fields)))
    | E_field (exp, (m, f)) ->
        (* A record field index is similar to a data constructor but
           has no arity check; its constraint makes its destructor
           type equal to the type taking [exp] to [t].*)
        let field = Location.value f in
        let _ = lookup_field_destructor tenv (Location.loc f)
                  (m, LName field) in
        let binding = constr_name_field_destructor m f in
        exists_aux (fun exvar ->
            let c', (wc', exp') = infer_expr tenv venv exp exvar in
            let typ = TypeConv.arrow tenv exvar t in
            c' ^ (SName binding <? typ) e.expr_loc,
            (wc',
             mk_auxexpr (E_field (exp', (m, f)))))
    | E_apply ({expr = E_mod_member (m, i); _} as f, [n])
         when Location.value m = "Bits"
              && (Location.value i = "ones"
                  || Location.value i = "zeros") ->
        (* special case handling of bitvector api *)
        (match n with
           | {expr = E_literal ((PL_int (w, _)) as lit); _} ->
               check_literal lit n.expr_loc;
               if   w <= 0
               then raise (Error (e.expr_loc, InvalidBitvectorWidth w));
               (* we only need the typed ast, not the constraints *)
               let int = typcon_variable tenv (std_type "usize") in
               let _, (_, n') = infer_expr tenv venv n int in
               (* we know the result type *)
               let v = TypeConv.bitvector_n tenv w in
               exists_aux ~pos:e.expr_loc (fun ex ->
                   (* we only need the typed ast, not the constraints *)
                   let ftyp = TypeConv.arrow tenv ex v in
                   let _, (_, f') = infer_expr tenv venv f ftyp in
                   (v =?= t) e.expr_loc,
                   (WC_true,
                    mk_auxexpr (E_apply (f', [n']))))
           | _ ->
               let err = Non_constant_numerical_arg (m, i) in
               raise (Error (n.expr_loc, err)))
    | E_apply (fexp, args) ->
        (* The constraint of an [apply] makes equal the type of the
           function expression [fexp] and the function type taking the
           types of arguments [args] to [t]. *)

        (* an empty argument list corresponds to an argument of unit *)
        if   List.length args = 0
        then let unit = typcon_variable tenv (std_type "unit") in
             let typ = TypeConv.arrow tenv unit t in
             let cfun, (wc_fun, fexp') = infer_expr tenv venv fexp typ in
             cfun, (wc_fun, mk_auxexpr (E_apply (fexp', [])))
        else exists_list_aux args (
                 fun exs ->
                 let typ, cargs, wcargs, args =
                   List.fold_left
                     (fun (typ, c, wc, args) (arg, exvar) ->
                       let c', (wc', arg') = infer_expr tenv venv arg exvar in
                       TypeConv.arrow tenv exvar typ,
                       c ^ c',
                       wc @^ wc',
                       arg' :: args)
                     (t, CTrue e.expr_loc, WC_true, [])
                     (List.rev exs) in
                 let cfun, (wc_fun, fexp') = infer_expr tenv venv fexp typ in
                 cfun ^ cargs,
                 (wc_fun @^ wcargs,
                  mk_auxexpr (E_apply (fexp', args))))
    | E_match (exp, (m, typ, dc)) ->
        (* Desugar this as a case expression:

           case (exp) {typ::c _ _ _ => true, _ => false}

           We cannot do it in the parser since we need to know the
           arity of the data constructor [typ::c] to generate the correct
           wildcard case pattern.  The return type is constrained to
           be boolean. *)
        let dcid, dcloc = Location.value dc, Location.loc dc in
        let dcid = AstUtils.canonicalize_dcon (Location.value typ) dcid in
        let arity, _, _ = lookup_datacon tenv dcloc (m, DName dcid) in
        let case_exp = make_match_case_expr m exp typ dc arity e.expr_loc in
        let bool_typ = type_of_primitive (as_fun tenv) (PL_bool true) in
        let c, (wc, case_exp') = infer_expr tenv venv case_exp t in
        (* extract the case scrutinee for the sugared output *)
        let exp' = match case_exp'.expr with
            | E_case (exp, _) -> exp
            | _               -> assert false in
        c ^ (t =?= bool_typ) e.expr_loc,
        (wc,
         mk_auxexpr (E_match (exp', (m, typ, dc))))
    | E_literal prim_lit ->
        check_literal prim_lit e.expr_loc;
        let primtyp = type_of_primitive (as_fun tenv) prim_lit in
        (t =?= primtyp) e.expr_loc,
        (WC_true,
         mk_auxexpr (E_literal prim_lit))
    | E_case (exp, clauses) ->
        (* The constraint of a [case] makes equal the type of the
           scrutinee and the type of every branch pattern. The body
           of each branch must be equal to [t]. *)
        exists_aux (fun exvar ->
            let ce, (wce, exp') = infer_expr tenv venv exp exvar in
            let clauses' =
              List.map
                (fun (p, b) ->
                  let fragment, p', venv' =
                    infer_pat_fragment tenv venv p exvar in
                  let cb, (wcb, b') = infer_expr tenv venv' b t in
                  CLet ([ Scheme (p.pattern_loc, [], fragment.vars,
                                  fragment.tconstraint,
                                  fragment.gamma) ],
                        cb),
                  (wcb, (p', b')))
                clauses in
            let ccl, clauses' = List.split clauses' in
            let wcl, clauses' = List.split clauses' in
            ce ^ conj ccl,
            (wce @^ wconj wcl,
             mk_auxexpr (E_case (exp', clauses'))))
    | E_let (p, def, body) ->
        (* The constraint of this non-generalizing [let] makes equal
           the type of the pattern and the definiens, and requires
           the type of the let body to be equal to [t]. *)
        exists_aux (fun exvar ->
            let fragment, p', venv' = infer_pat_fragment tenv venv p exvar in
            let cdef, (wcdef, def') = infer_expr tenv venv def exvar in
            (* Require [t] to be a valid type for [body]. *)
            let cbody, (wcbody, body') = infer_expr tenv venv' body t in
            cdef
            ^ CLet ([ Scheme (e.expr_loc, [], fragment.vars,
                              (* Require [exvar] to be a valid type
                                 for [p]. *)
                              fragment.tconstraint,
                              fragment.gamma) ],
                    cbody),
            (wcdef @^ wcbody,
             mk_auxexpr (E_let (p', def', body'))))
    | E_cast (exp, typ) ->
        (* A type constraint inserts a type equality into the
           generated constraint. *)
        let ityp = intern_expanded_type tenv typ in
        let c, (wc, exp') = infer_expr tenv venv exp ityp in
        (t =?= ityp) e.expr_loc ^ c,
        (wc,
         mk_auxexpr (E_cast (exp', typ)))
    | E_print (b, e) ->
        exists_aux (fun t' ->
            let ce, (wce, e') = infer_expr tenv venv e t' in
            let u = typcon_variable tenv (std_type "unit") in
            let cu = (t =?= u) e.expr_loc in
            ce ^ cu, (wce, mk_auxexpr (E_print (b, e'))))
    | E_unop (op, e) ->
        (* This is a special case of a constructor application. *)
        exists_aux (fun exvar ->
            let opid = unop_const_name op in
            let typ = TypeConv.arrow tenv exvar t in
            let c, (wc, e') = infer_expr tenv venv e exvar in
            c ^ (SName opid <? typ) e.expr_loc,
            (wc,
             mk_auxexpr (E_unop (op, e'))))
    | E_binop (op, le, re) ->
        exists_aux (fun lexvar ->
            exists_aux (fun rexvar ->
                let opid = binop_const_name op in
                let typ = TypeConv.arrow tenv lexvar
                            (TypeConv.arrow tenv rexvar t) in
                let cle, (wcle, le') = infer_expr tenv venv le lexvar in
                let cre, (wcre, re') = infer_expr tenv venv re rexvar in
                cle ^ cre ^ (SName opid <? typ) e.expr_loc,
                (wcle @^ wcre,
                 mk_auxexpr (E_binop (op, le', re')))))
    | E_recop ((m, rtyp, op), e') when Location.value op = "bits" ->
        (* We need the following constraints:
         * . rtyp should be a bitfield record for bitvector<n>
         * . e' should be of type rtyp
         * . result should be of type bitvector<n>
         *)
        let bf_len = TypedAstUtils.lookup_bitfield_length tenv m rtyp in
        let v = TypeConv.bitvector_n tenv bf_len in
        let rt =
          TypeConv.intern tenv (AstUtils.make_tname_id m rtyp) in
        let ce, (wce, e') = infer_expr tenv venv e' rt in
        ce ^ (v =?= t) e.expr_loc,
        (wce, mk_auxexpr (E_recop ((m, rtyp, op), e')))
    | E_recop ((m, rtyp, op), e') when Location.value op = "record" ->
        (* We need the following constraints:
         * . rtyp should be a bitfield record for bitvector<n>
         * . e' should be of type bitvector<n>
         * . result should be of type rtyp
         *)
        let bf_len = TypedAstUtils.lookup_bitfield_length tenv m rtyp in
        let v = TypeConv.bitvector_n tenv bf_len in
        let rt =
          TypeConv.intern tenv (AstUtils.make_tname_id m rtyp) in
        let ce, (wce, e') = infer_expr tenv venv e' v in
        ce ^ (rt =?= t) e.expr_loc,
        (wce, mk_auxexpr (E_recop ((m, rtyp, op), e')))
    | E_recop ((_, _, op), _) ->
        let loc = Location.loc op in
        let op  = Location.value op in
        let err = InvalidRecordOperator op in
        raise (Error (loc, err))
    | E_bitrange (bve, n, m) ->
        if   m < 0
        then (let err = InvalidBitrangeLowBound m in
              raise (Error (e.expr_loc, err)));
        if   m > n
        then (let err = InvalidEmptyBitrange (n, m) in
              raise (Error (e.expr_loc, err)));
        let w = n - m + 1 in
        let v = TypeConv.bitvector_n tenv w in
        let x = variable Flexible ~pos:bve.expr_loc () in
        let exvar = CoreAlgebra.TVariable x in
        let v' = TypeConv.bitvector_t tenv exvar in
        let ce, (wce, bve') = infer_expr tenv venv bve v' in
        let c = (v =?= t) e.expr_loc ^ ce in
        let wc = wce @^ (WC_pred (e.expr_loc, x, WP_more n)) in
        (ex ~pos:e.expr_loc [x] c),
        (wc, mk_auxexpr (E_bitrange (bve', n, m)))
    | E_mod_member (m, i) ->
        let loc = Location.extent (Location.loc m) (Location.loc i) in
        let mid = Modul (Mod_explicit m) in
        let vid = Location.value i in
        let v = AstUtils.make_var i in
        check_accessible loc tenv (mid, VName vid) (VEnv.cur_module venv);
        let id = constr_name_mod_value mid v in
        (SName id <? t) loc,
        (WC_true,
         mk_auxexpr (E_mod_member (m, i)))

(* wrappers for add_value *)
let add_value, add_foreign =
  (fun tenv loc vid typ -> add_value tenv loc vid typ false),
  (fun tenv loc vid typ -> add_value tenv loc vid typ true)

(* [infer_const_defn tenv venv ctxt cd] examines the const definition [fd]
   and constraint context [ctxt] in the type environment [tenv] and
   value environment [venv] and generates an updated constraint
   context for [ctxt] and a type signature for [cd]. *)
let infer_const_defn tenv venv ctxt cd =
  let loc = Location.loc cd.const_defn_ident in
  let cn  = var_name cd.const_defn_ident in
  (* Introduce a type variable for the constant signature. *)
  let cv = variable Flexible () in
  let ctyp = CoreAlgebra.TVariable cv in
  (* Create a value variable for the constant *)
  let cn', _ = VEnv.add venv cd.const_defn_ident in
  (* Expand and intern the specified type *)
  let ityp = intern_expanded_type tenv cd.const_defn_type in
  (* Generate the typing constraint for the value expression *)
  let cval, (wcval, val') =
    infer_expr tenv venv cd.const_defn_val ityp in
  (* Bind the type variable for the full constraint *)
  let cc = (ctyp =?= ityp) cd.const_defn_loc ^ cval in
  let m  = infer_mod cd.const_defn_mod in
  let bind = constr_name_mod_value m cd.const_defn_ident in
  let env = StringMap.singleton bind (ctyp, loc) in
  (* Construct the binding for the value definition. *)
  let scheme = Scheme (cd.const_defn_loc, [], [cv], cc, env) in
  (* Enter value into the typing environment. *)
  add_value tenv loc (m, VName cn) ([], ctyp),
  (* Generate the constraint context *)
  (fun c -> ctxt (CLet ([scheme], c))),
  wcval,
  (* The annotated constant *)
  {const_defn_ident = cn';
   const_defn_type  = cd.const_defn_type;
   const_defn_val   = val';
   const_defn_mod   = cd.const_defn_mod;
   const_defn_loc   = loc;
   const_defn_aux   = ityp}

(* [infer_fun_defn tenv venv ctxt fd] examines the function definition
   [fd] and constraint context [ctxt] in the type environment [tenv]
   and value environment [venv] and generates an updated constraint
   context for [ctxt] and a type signature for [fd]. *)
let infer_fun_defn tenv venv ctxt fd =
  let loc = Location.loc fd.fun_defn_ident
  and fdn = var_name fd.fun_defn_ident
  and m  = infer_mod fd.fun_defn_mod
  and qs = fd.fun_defn_tvars in
  let qs = List.map (fun q -> stdlib, TName (Location.value q)) qs in
  let rqs, rtenv = fresh_unnamed_rigid_vars fd.fun_defn_loc tenv qs in
  let tenv' = add_type_variables rtenv tenv in

  (* Introduce a type variable for the function signature. *)
  let fv = variable Flexible () in
  let ftyp = CoreAlgebra.TVariable fv in
  (* Value type in the typing environment. *)
  let vtyp = rqs, ftyp in

  (* Prevent duplicate definitions.  The functional sublanguage is
     processed before the grammar sublanguage; as a result, functions
     have global scope in the grammar sublanguage as opposed to
     lexical scope.  This creates a problem with duplicate function
     definitions: only the last definition of 'f' will be used at all
     calls to 'f', even though an earlier definition of 'f' may be in
     lexical scope at a call.  This can result in very confusing error
     messages.  Address this problem by forbidding duplicate
     definitions. *)
  (match VEnv.lookup venv fd.fun_defn_ident with
     | None   -> ()
     | Some v -> let loc' = Location.loc v in
                 raise (Error (loc, DuplicateFunctionDefinition (fdn, loc'))));

  (* for recursive functions, make sure the function name is bound *)
  let fdn', venv' = VEnv.add venv fd.fun_defn_ident in
  let tenv', venv', ids =
    if   fd.fun_defn_recursive
    then add_value tenv' loc (m, VName fdn) vtyp,
         venv',
         StringMap.singleton fdn (ident_of_var fd.fun_defn_ident)
    else tenv',
         venv,
         StringMap.empty in

  (* First construct the function signature and the argument bindings
     for the body.  Handle the arguments as a simple case of lambda
     patterns; this will allow us to extend this later to proper
     pattern matching if needed.*)
  let irestyp = intern_expanded_type tenv' fd.fun_defn_res_type in
  let _, params', venv', argbinders, signature =
    if   List.length fd.fun_defn_params = 0
    then (* functions without args have a signature of unit -> result_type *)
         let unit = typcon_variable tenv' (std_type "unit") in
         let signature = TypeConv.arrow tenv' unit irestyp in
         ids, [], venv', empty_fragment, signature
    else List.fold_left (fun (acu_ids, params', venv', bindings, signature)
                             (pid, typ, _) ->
             let pn, ploc = var_name pid, Location.loc pid in
             let acu_ids =
               match StringMap.find_opt pn acu_ids with
                 | Some repid ->
                     let pid = ident_of_var pid in
                     let loc = Location.loc pid in
                     raise (Error (loc, RepeatedFunctionParameter (pid, repid)))
                 | None ->
                     StringMap.add pn (ident_of_var pid) acu_ids in
             let pid', venv' = VEnv.add venv' pid in
             let ityp = intern_expanded_type tenv' typ in
             let v = variable Flexible () in
             acu_ids,
             (pid', typ, ityp) :: params',
             venv',
             {gamma = StringMap.add pn (CoreAlgebra.TVariable v, ploc)
                        bindings.gamma;
              tconstraint = (CoreAlgebra.TVariable v =?= ityp) ploc
                            ^ bindings.tconstraint;
              vars = v :: bindings.vars},
             TypeConv.arrow tenv' ityp signature)
           (ids, [], venv', empty_fragment, irestyp)
           (List.rev fd.fun_defn_params) in

  (* for recursive functions, add the function name to the let context. *)
  let gamma = if   fd.fun_defn_recursive
              then StringMap.add fdn (ftyp, loc) argbinders.gamma
              else argbinders.gamma in
  let arg_schm = Scheme (fd.fun_defn_loc, [], argbinders.vars,
                         argbinders.tconstraint,
                         gamma) in

  (* Generate the typing constraint for the body. *)
  let cbody, (wcbody, body') = infer_expr tenv' venv' fd.fun_defn_body irestyp in

  (* Construct the constrained binding for the polymorphic function
     definition itself. *)
  let scheme =
    let def_c = CLet ([arg_schm],
                      (ftyp =?= signature) loc
                      ^ cbody) in
    let bind = constr_name_mod_value m fd.fun_defn_ident in
    let env = StringMap.singleton bind (ftyp, loc) in
    Scheme (fd.fun_defn_loc, rqs, [fv], def_c, env) in

  (* Enter value into the typing environment. *)
  add_value tenv loc (m, VName fdn) vtyp,
  (* Generate the constraint context. *)
  (fun c -> ctxt (CLet ([scheme], c))),
  wcbody,
  (* The annotated function contains the function signature and the
   * annotated body. *)
  {fun_defn_ident     = fdn';
   fun_defn_tvars     = fd.fun_defn_tvars;
   fun_defn_params    = params';
   fun_defn_res_type  = fd.fun_defn_res_type;
   fun_defn_body      = body';
   fun_defn_recursive = fd.fun_defn_recursive;
   fun_defn_synth     = fd.fun_defn_synth;
   fun_defn_mod       = fd.fun_defn_mod;
   fun_defn_loc       = fd.fun_defn_loc;
   fun_defn_aux       = signature}

(* [infer_recfun_defns tenv venv ctxt fds] examines the mutually
   recursive function definitions [fds] and constraint context [ctxt]
   in the type environment [tenv] and value environment [venv] and
   generates an updated constraint context for [ctxt] and a type
   signature for each function in [fds]. *)

let infer_recfun_defns tenv venv ctxt r =
  (* Do a first pass over the function signatures, collecting variable
     and binding environments in which only the function names and
     their signatures are bound.  These will be the common base from
     which the environments to type each function body will be built.

     This differs from the handling for a single function, which can
     be processed in a single pass.  *)
  let vinfos, tenv', venv', fdns', rqs, fvs, sigs, env, eqns =
    List.fold_left
      (fun (vinfos, tenv, venv, fdns', rqs, fvs, sigs, env, eqns) fd ->
        let loc = Location.loc fd.fun_defn_ident
        and fdn = var_name fd.fun_defn_ident
        and qs = fd.fun_defn_tvars in
        (* Prevent duplicate definitions *)
        (match VEnv.lookup venv fd.fun_defn_ident with
           | None ->
               ()
           | Some v ->
               let lc' = Location.loc v in
               let err = DuplicateFunctionDefinition (fdn, lc') in
               raise (Error (loc, err)));
        (* Bind the function name *)
        let fdn', venv' = VEnv.add venv fd.fun_defn_ident in
        (* Collect the type variables to quantify over, and register
           them in the type environment *)
        let qs = List.map (fun q -> stdlib, TName (Location.value q)) qs in
        let rqs', rtenv' =
          fresh_unnamed_rigid_vars fd.fun_defn_loc tenv qs in
        let tenv' = add_type_variables rtenv' tenv in
        (* Construct the function signature.  Check for duplicate
           parameter names here, but ignore creating their variable
           bindings: those will need to be added to a per-function
           body venv that does not contain parameter information from
           other function bodies, but does include all the function
           names, and we haven't seen all the function names yet. *)
        let irestyp = intern_expanded_type tenv' fd.fun_defn_res_type in
        let signature, _ =
          if   List.length fd.fun_defn_params = 0
          then (* functions without args have a signature of unit -> result_type *)
               let unit = typcon_variable tenv' (std_type "unit") in
               let signature = TypeConv.arrow tenv' unit irestyp in
               signature, StringMap.empty
          else List.fold_left (fun (signature, ids) (pid, typ, _) ->
                   let pn = var_name pid in
                   let ids =
                     match StringMap.find_opt pn ids with
                       | Some rid ->
                           let pid = ident_of_var pid in
                           let e = RepeatedFunctionParameter (pid, rid) in
                           let loc = Location.loc pid in
                           raise (Error (loc, e))
                       | None ->
                           StringMap.add pn (ident_of_var pid) ids in
                   let ityp = intern_expanded_type tenv' typ in
                   let signature = TypeConv.arrow tenv' ityp signature in
                   signature, ids)
                 (irestyp, StringMap.empty)
                 (List.rev fd.fun_defn_params) in
        (* Create a type variable for this signature, and add it to
           the top-level bindings *)
        let fv = variable Flexible () in
        let ftv = CoreAlgebra.TVariable fv in
        (* Value type for the typing environment. *)
        let vtyp = rqs, ftv in
        let m = infer_mod fd.fun_defn_mod in
        let vinfo = loc, (m, VName fdn), vtyp in
        let tenv' = add_value tenv' loc (m, VName fdn) vtyp in
        let bind = constr_name_mod_value m fd.fun_defn_ident in
        let env = StringMap.add bind (ftv, loc) env in
        let eqn = (ftv =?= signature) loc in
        vinfo :: vinfos, tenv', venv', fdn' :: fdns', rqs' @ rqs, fv :: fvs,
        signature :: sigs, env, eqn :: eqns)
      ([], tenv, venv, [], [], [], [], StringMap.empty, [])
      (List.rev r.recfuns) in

  (* Now that we have the base environments that include the function
     names and signatures, make a second pass to process the function
     bodies.  This differs from the handling of non-recursive
     functions, whose bodies need environments that do not include the
     function. *)
  let fdinfos = List.combine fdns' (List.combine sigs r.recfuns) in
  let cs, wc, fds' =
    List.fold_left (fun (cs, wc, fds') (fdn', (sgn, fd)) ->
        let params', venv', argbinders =
          List.fold_left
            (fun (params', venv', argbinders) (pid, typ, _) ->
              let pn, ploc = var_name pid, Location.loc pid in
              (* We've already checked for param duplicates above *)
              let pid', venv' = VEnv.add venv' pid in
              let v = variable Flexible () in
              let ityp = intern_expanded_type tenv' typ in
              (pid', typ, ityp) :: params',
              venv',
              {gamma =
                 StringMap.add pn (CoreAlgebra.TVariable v, ploc)
                   argbinders.gamma;
               tconstraint = (CoreAlgebra.TVariable v =?= ityp) ploc
                             ^ argbinders.tconstraint;
               vars = v :: argbinders.vars})
            (* venv' and env already contain the function bindings *)
            ([], venv', {empty_fragment with gamma = env})
            (List.rev fd.fun_defn_params) in
        (* Construct the binding context for the body type constraint *)
        let arg_schm =
          Scheme (fd.fun_defn_loc, [], argbinders.vars,
                  argbinders.tconstraint, argbinders.gamma) in
        (* Generate the body type constraint *)
        let irtyp = intern_expanded_type tenv' fd.fun_defn_res_type in
        let cbody, (wcbody, body') =
          infer_expr tenv' venv' fd.fun_defn_body irtyp in
        let c = CLet ([arg_schm],
                      conj eqns ^ cbody) in
        let fd' =
          {fun_defn_ident     = fdn';
           fun_defn_tvars     = fd.fun_defn_tvars;
           fun_defn_params    = params';
           fun_defn_res_type  = fd.fun_defn_res_type;
           fun_defn_body      = body';
           fun_defn_recursive = fd.fun_defn_recursive;
           fun_defn_synth     = fd.fun_defn_synth;
           fun_defn_mod       = fd.fun_defn_mod;
           fun_defn_loc       = fd.fun_defn_loc;
           fun_defn_aux       = sgn} in
        c :: cs,
        wcbody @^ wc,
        fd' :: fds'
      ) ([], WC_true, []) (List.rev fdinfos) in
  (* Enter values into environment *)
  let tenv = List.fold_left (fun tenv (l, vid, vtyp) ->
                 add_value tenv l vid vtyp
               ) tenv vinfos in
  (* Now combine the constraints *)
  let scheme =
    let rc = conj cs in
    Scheme (r.recfuns_loc, rqs, fvs, rc, env) in
  tenv,
  (fun c -> ctxt (CLet ([scheme], c))),
  wc,
  {r with recfuns = fds'}

(* [infer_ffi_decl tenv venv ctxt fd] examines the foreign function
   declaration [fd] and constraint context [ctxt] in the type
   environment [tenv] and value environment [venv] and generates an
   updated constraint context for [ctxt] and a type signature for
   [fd]. *)
let infer_ffi_decl tenv venv ctxt fd =
  let loc = Location.loc fd.ffi_decl_ident
  and fdn = var_name fd.ffi_decl_ident
  and m  = infer_mod fd.ffi_decl_mod in

  (* Introduce a type variable for the function signature. *)
  let fv = variable Flexible () in
  let ftyp = CoreAlgebra.TVariable fv in
  (* Value type in the typing environment. *)
  let vtyp = [], ftyp in

  (* Prevent duplicate definitions.  The functional sublanguage is
     processed before the grammar sublanguage; as a result, functions
     have global scope in the grammar sublanguage as opposed to
     lexical scope.  This creates a problem with duplicate function
     definitions: only the last definition of 'f' will be used at all
     calls to 'f', even though an earlier definition of 'f' may be in
     lexical scope at a call.  This can result in very confusing error
     messages.  Address this problem by forbidding duplicate
     definitions. *)
  (match VEnv.lookup venv fd.ffi_decl_ident with
     | None   -> ()
     | Some v -> let loc' = Location.loc v in
                 raise (Error (loc, DuplicateFunctionDefinition (fdn, loc'))));

  (* Adapt `infer_fun_defn`: non-recursive defn. *)
  let fdn', _venv' = VEnv.add venv fd.ffi_decl_ident in
  let tenv', venv', ids =
    tenv, venv, StringMap.empty in

  (* First construct the function signature and the argument bindings. *)
  let irestyp = intern_expanded_type tenv' fd.ffi_decl_res_type in
  let _, params', _, argbinders, signature =
    if   List.length fd.ffi_decl_params = 0
    then (* functions without args have a signature of unit -> result_type *)
         let unit = typcon_variable tenv' (std_type "unit") in
         let signature = TypeConv.arrow tenv' unit irestyp in
         ids, [], venv', empty_fragment, signature
    else List.fold_left (fun (acu_ids, params', venv', bindings, signature)
                             (pid, typ, _) ->
             let pn, ploc = var_name pid, Location.loc pid in
             let acu_ids =
               match StringMap.find_opt pn acu_ids with
                 | Some repid ->
                     let pid = ident_of_var pid in
                     let loc = Location.loc pid in
                     raise (Error (loc, RepeatedFunctionParameter (pid, repid)))
                 | None ->
                     StringMap.add pn (ident_of_var pid) acu_ids in
             let pid', venv' = VEnv.add venv' pid in
             let ityp = intern_expanded_type tenv' typ in
             let v = variable Flexible () in
             acu_ids,
             (pid', typ, ityp) :: params',
             venv',
             {gamma = StringMap.add pn (CoreAlgebra.TVariable v, ploc)
                        bindings.gamma;
              tconstraint = (CoreAlgebra.TVariable v =?= ityp) ploc
                            ^ bindings.tconstraint;
              vars = v :: bindings.vars},
             TypeConv.arrow tenv' ityp signature)
           (ids, [], venv', empty_fragment, irestyp)
           (List.rev fd.ffi_decl_params) in

  (* Adapt `infer_fun_defn`: non-recursive function. *)
  let gamma = argbinders.gamma in
  let arg_schm = Scheme (fd.ffi_decl_loc, [], argbinders.vars,
                         argbinders.tconstraint,
                         gamma) in

  (* Construct the constrained binding for the function definition
     itself. *)
  let scheme =
    let def_c = CLet ([arg_schm],
                      (ftyp =?= signature) loc) in
    let bind = constr_name_mod_value m fd.ffi_decl_ident in
    let env = StringMap.singleton bind (ftyp, loc) in
    Scheme (fd.ffi_decl_loc, [], [fv], def_c, env) in

  (* Enter foreign value into the typing environment. *)
  add_foreign tenv loc (m, VName fdn) vtyp,
  (* Generate the constraint context. *)
  (fun c -> ctxt (CLet ([scheme], c))),
  (* The annotated function contains the function signature. *)
  {ffi_decl_ident     = fdn';
   ffi_decl_params    = params';
   ffi_decl_res_type  = fd.ffi_decl_res_type;
   ffi_decl_langs     = fd.ffi_decl_langs;
   ffi_decl_mod       = fd.ffi_decl_mod;
   ffi_decl_loc       = fd.ffi_decl_loc;
   ffi_decl_aux       = signature}

(** [guess_nt_rhs_type tenv ntd] tries to guess a type for the
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
let guess_nt_rhs_type tenv ntd =
  let res =
    match ntd.non_term_rules with
      (* a single production with a single non-terminal *)
      | [{rule_rhs = [{rule_elem = RE_non_term (m, n, _); _}]; _}] ->
          lookup_non_term_type tenv (m, NName (Location.value n))
      (* each production is a sequence of unnamed regular expressions *)
      | rules ->
          let is_regexp =
            List.for_all (fun r ->
                List.for_all TypedAstUtils.guess_is_regexp_elem r.rule_rhs
              ) rules in
          if   is_regexp
          then let byte  = typcon_variable tenv (std_type "byte") in
               Some (list (typcon_variable tenv) byte)
          else None in
  match res with
    | Some t ->
        t
    | None ->
        let loc = Location.loc ntd.non_term_name in
        raise (Error (loc, NTTypeNotInferrable ntd.non_term_name))

let infer_non_term_attrs tenv nid attrs =
  let map, attrs', _ =
    List.fold_left (fun (ats, attrs', venv') (pid, te, _) ->
        let p = var_name pid in
        let t = intern_expanded_type tenv te in
        match StringMap.find_opt p ats with
          | Some (_, l) ->
              let repid = Location.mk_loc_val p l in
              let pid = ident_of_var pid in
              let loc = Location.loc pid in
              raise (Error (loc, NTRepeatedBinding (nid, pid, repid)))
          | None ->
              let pid', venv' = VEnv.add venv' pid in
              StringMap.add p (t, Location.loc pid) ats,
              (pid', te, t) :: attrs',
              venv')
      (StringMap.empty, [], VEnv.empty)
      attrs in
  map, List.rev attrs'

let infer_non_term_inh_type tenv ntd =
  let nid   = ntd.non_term_name in
  let attrs = ntd.non_term_inh_attrs in
  infer_non_term_attrs tenv nid attrs

(** [infer_non_term_type tenv ctxt ntd] updates [tenv] with a record
   type for a non-terminal (NT) [ntd] corresponding to its attributes,
   and updates ctxt with the names of the corresponding field
   destructors. *)
let infer_non_term_type tenv ctxt ntd =
  let ntid  = ntd.non_term_name
  and loc   = ntd.non_term_loc in
  let ntnm  = Location.value ntid
  and ntpos = Location.loc ntid
  and m     = infer_mod ntd.non_term_mod in
  let inh_typ = infer_non_term_inh_type tenv ntd in
  match ntd.non_term_syn_attrs with
    | ALT_type t ->
        (* t should be a record type, and the NT should be
           given a flexible variable which is equated to [[t]]. *)
        let tn = Location.value t in
        let tloc = Location.loc t in
        let recinfo = match get_record_info tenv (m, TName tn) with
            | Some info ->
                Some info
            | None ->
                let loc = Location.loc t in
                raise (Error (loc, NTAttributesNotRecordType (ntid, t))) in
        let tvar  = lookup_type_variable ~pos:tloc tenv (m, TName tn) in
        (* This NT cannot be used as a type constructor since it is
           aliased to the defined type, and it is represented by a
           flexible variable to create a solvable constraint. If we
           need to use NT as a type constructor, we will have to
           modify the tycon lookup logic in the typing environment
           to not require Constant variables. *)
        let ivar  = variable ~name:(m, TName ntnm) Flexible () in
        let cnstr = (CoreAlgebra.TVariable ivar =?= tvar) tloc in
        let ntt   = (inh_typ, NTT_type (CoreAlgebra.TVariable ivar, recinfo)) in
        let tenv' = add_non_terminal tenv ntpos (m, NName ntnm) ntt in
        let ctxt' = (fun c ->
            ctxt (CLet ([Scheme (loc, [], [ivar], cnstr ^ c, StringMap.empty)],
                        CTrue loc))) in
        tenv', ctxt'
    | ALT_decls [] ->
        (* No type is declared; so it needs to be inferred.  This NT
           cannot be used as a type constructor. *)
        let tvar  = guess_nt_rhs_type tenv ntd in
        let ivar  = variable ~name:(m, TName ntnm) Flexible () in
        let cnstr = (CoreAlgebra.TVariable ivar =?= tvar) ntd.non_term_loc in
        let ntt   = (inh_typ, NTT_type (CoreAlgebra.TVariable ivar, None)) in
        let tenv' = add_non_terminal tenv ntpos (m, NName ntnm) ntt in
        let ctxt' = (fun c ->
            ctxt (CLet ([Scheme (loc, [], [ivar], cnstr ^ c, StringMap.empty)],
                        CTrue loc))) in
        tenv', ctxt'
    | ALT_decls attrs ->
        (* The NT is given a new monomorphic record type corresponding
           to the explicitly declared attributes.  This allows the NT
           to be usable as a type constructor. *)
        let ikind = KindInferencer.intern_kind (as_kind_env tenv) KStar in
        let ivar  = variable ~name:(m, TName ntnm) Constant () in
        let adt   = ref None in
        let tenv  = add_type_constructor tenv ntpos (m, TName ntnm)
                      (ikind, ivar, adt) in
        let rcd   = ref None in
        let ntt   = (inh_typ, NTT_record (ivar, rcd)) in
        let tenv' = add_non_terminal tenv ntpos (m, NName ntnm) ntt in
        let ctxt' = (fun c ->
            ctxt (CLet ([Scheme (loc, [ivar], [], c, StringMap.empty)],
                        CTrue loc))) in
        let attrs = List.map (fun (id, te, _, _) ->
                        id, TypedAstUtils.expand_type_abbrevs tenv te
                      ) attrs in
        let tenv', dids, drqs, let_env =
          List.fold_left
            (intern_field_destructor m ntid [])
            (tenv', [], [], StringMap.empty)
            attrs in
        let tenv', cid, crqs, let_env =
          intern_record_constructor m ntid []
            (tenv', let_env) attrs in
        let rec_info = {adt                = ntid;
                        modul              = m;
                        fields             = attrs;
                        record_constructor = cid;
                        field_destructors  = dids;
                        bitfield_info      = None} in
        rcd := Some rec_info;
        adt := Some {adt = Record rec_info; loc};
        let ctxt' = (fun c ->
            ctxt' (CLet ([Scheme (loc, drqs @ crqs, [], CTrue loc, let_env)],
                         c))) in
        tenv', ctxt'

let check_non_term tenv m id t =
  let n = Location.value id in
  match lookup_non_term_type tenv (m, NName n) with
    | None ->
        raise (Error (Location.loc id, UnknownNonTerminal id))
    | Some t' ->
        (t =?= t') (Location.loc id)

(* The next few functions deal with processing literals in regular
   expressions.  The main tasks in this processing are:

   . Converting any embedded escape sequences using a specialized
     lexer.  The converted literal then replaces the original in the
     AST.

   . Checking membership of character classes for the difference
     operator.
 *)

(* Use a specialized lexer to convert any embedded escapes in string
   literals into their char denotations; return both the converted
   and original literals for better error reporting. *)
let convert_escapes (s : literal) : literal * literal =
  let loc = Location.loc s in
  let lexbuf = Lexing.from_string (Location.value s) in
  let start = Location.get_start loc in
  let cnum = start.pos_cnum in
  (* tweak for more accurate error message *)
  let cnum = if cnum <= 0 then 0 else cnum - 1 in
  let lexbuf = {lexbuf with
                 (* adjust lexer's notion of position *)
                 lex_abs_pos = cnum;
                 lex_curr_p = {start with pos_cnum = cnum}} in
  Literal_lexer.reset_literal ();
  let l = Literal_lexer.literal lexbuf in
  Location.mk_loc_val l loc, s

(* This assumes the character class [id] has been checked to be
   defined. *)
let check_in_character_class id (ls : (literal * literal) list) =
  let chars = List.assoc (Location.value id) character_classes in
  List.iter (fun (l, l') ->
      let c = Location.value l in
      if   String.length c != 1
      then raise (Error (Location.loc l', Not_a_character l'));
      if   not (Array.mem c.[0] chars)
      then raise (Error (Location.loc l, Not_in_character_set (id, l)))
    ) ls

(* checking a literal set generates a type constraint and the
   escape-converted literal set *)
let check_literals tenv ls t : tconstraint * mod_qual literal_set =
  let byte  = typcon_variable tenv (std_type "byte") in
  let bytes = list (typcon_variable tenv) byte in
  match ls.literal_set with
    (* two types of identifiers are allowed as literals:
       character-classes, and non-terminals that are defined as
       regular expressions.
     *)
    | LS_type (m, id) when m = AstUtils.stdlib && is_character_class id ->
        (t =?= bytes) ls.literal_set_loc, ls
    | LS_type (m, id) ->
        check_non_term tenv m id t, ls

    (* Set difference is only supported for elision of single
       characters from character classes.  i.e. the left operand
       needs to be a character class, and the right a union of
       single characters *)
    | LS_diff (({literal_set = LS_type (m, cc); _} as lls),
               ({literal_set = LS_set ls'; _} as rls))
         when m = AstUtils.stdlib ->
        if   not (is_character_class cc)
        then raise (Error (Location.loc cc, Unknown_character_class cc));
        let ls' = List.map convert_escapes ls' in
        check_in_character_class cc ls';
        let ls', _ = List.split ls' in
        let rls = {rls with literal_set = LS_set ls'} in
        (t =?= bytes) ls.literal_set_loc,
        {ls with literal_set = LS_diff (lls, rls)}
    | LS_diff ({literal_set = LS_type _; _}, {literal_set_loc = l'; _}) ->
        raise (Error (l', Not_literal_set))
    | LS_diff (l, _) ->
        raise (Error (l.literal_set_loc, Not_character_class))

    | LS_range (s, e) ->
        let (s, so), (e, eo) = convert_escapes s, convert_escapes e in
        (* Both start and end literals should have the same length,
           and the literal at each position of `s` should be <= the
           corresponding literal of `e`. *)
        let ss = Location.value s in
        let es = Location.value e in
        let sl, el = String.length ss, String.length es in
        if   sl != el
        then raise (Error (ls.literal_set_loc,
                           Inconsistent_range_literals (so, eo, sl, el)));
        let i = ref 0 in
        while !i != sl do
          (if   Char.code ss.[!i] > Char.code es.[!i]
           then let err = Inconsistent_literal_range (so, eo, !i) in
                raise (Error (ls.literal_set_loc, err)));
          incr i;
        done;
        (t =?= bytes) ls.literal_set_loc,
        {ls with literal_set = LS_range (s, e)}
    | LS_set ls' ->
        let ls', _ = List.split (List.map convert_escapes ls') in
        (* Literals will always be byte lists *)
        (t =?= bytes) ls.literal_set_loc,
        {ls with literal_set = LS_set ls'}

let rec infer_regexp tenv venv re t =
  let byte    = typcon_variable tenv (std_type "byte") in
  let bytes   = list (typcon_variable tenv) byte in
  let default = (t =?= bytes) re.regexp_loc in
  let mk_auxregexp re' =
    {regexp     = re';
     regexp_mod = re.regexp_mod;
     regexp_loc = re.regexp_loc;
     regexp_aux = t} in
  match re.regexp with
    | RX_literals ls ->
        let c, ls' = check_literals tenv ls t in
        c, (WC_true, mk_auxregexp (RX_literals ls'))

    | RX_empty
    | RX_wildcard ->
        default, (WC_true, mk_auxregexp RX_wildcard)

    | RX_type (m, id) ->
        (* This non-terminal should have a byte list type *)
        check_non_term tenv m id bytes,
        (WC_true,
         mk_auxregexp (RX_type (m, id)))

    (* The typing of Star here assumes that the individual matches for
       [re'] can be flattened into a byte list type for [re' *].  That
       is, if [re'] |- list byte, then [re' *] |- list byte due to the
       flattening.  To achieve this, we only need to ensure that [re']
       can be typed for some [t'], and ensure that the types of the
       base cases of RX_ are byte lists. *)
    | RX_star (re', None) ->
        let c, (wc, re'') =
          exists_aux (fun t' -> infer_regexp tenv venv re' t') in
        c ^ default,
        (wc,
         mk_auxregexp (RX_star (re'', None)))
    | RX_star (re', Some e) ->
        let int = typcon_variable tenv (std_type "usize") in
        let ce, (wce, e') = infer_expr tenv venv e int in
        let cre, (wcre, re'') =
          exists_aux (fun t' -> infer_regexp tenv venv re' t') in
        ce ^ cre ^ default,
        (wce @^ wcre,
         mk_auxregexp (RX_star (re'', Some e')))

    | RX_opt re' ->
        let c, (wc, re'') = infer_regexp tenv venv re' t in
        c, (wc, mk_auxregexp (RX_opt re''))

    (* For the same reasons as for Star above, we only ensure that the
       individual matches can be typed, and provide a byte list type
       for the overall type. *)
    | RX_choice rels ->
        exists_list_aux rels (fun exs ->
            let rels' =
              List.map (fun (re', t') -> infer_regexp tenv venv re' t') exs in
            let cs, rels' = List.split rels' in
            let wcs, rels' = List.split rels' in
            conj cs ^ default,
            (wconj wcs,
             mk_auxregexp (RX_choice rels')))
    | RX_seq rels ->
        exists_list_aux rels (fun exs ->
            let rels' =
              List.map (fun (re', t') -> infer_regexp tenv venv re' t') exs in
            let cs, rels' = List.split rels' in
            let wcs, rels' = List.split rels' in
            conj cs ^ default,
            (wconj wcs,
             mk_auxregexp (RX_seq rels')))

let rec infer_stmt tenv venv s =
  let make_stmt s' = {stmt = s'; stmt_loc = s.stmt_loc} in
  match s.stmt with
    | S_assign (l, r) ->
        (* Ensure that there is a type [t'] that is compatible with
           both sides of the assignment. *)
        exists_aux (fun t' ->
            let cl, (wcl, l') = infer_expr tenv venv l t' in
            let cr, (wcr, r') = infer_expr tenv venv r t' in
            cl ^ cr,(wcl @^ wcr,  make_stmt (S_assign (l', r'))))
    | S_let (p, def, ss) ->
        exists_aux (fun t' ->
            let fragment, p', venv' = infer_pat_fragment tenv venv p t' in
            let cdef, (wcdef, def') = infer_expr tenv venv def t' in
            let css, ss' = List.split (List.map (infer_stmt tenv venv') ss) in
            let wcss, ss' = List.split ss' in
            cdef
            ^ CLet ([ Scheme (s.stmt_loc, [], fragment.vars,
                              fragment.tconstraint,
                              fragment.gamma) ],
                    conj css),
            (wcdef @^ wconj wcss,
             make_stmt (S_let (p', def', ss'))))
    | S_case (e, clauses) ->
        (* Similar to E_case *)
        exists_aux (fun t' ->
            let ce, (wce, e') = infer_expr tenv venv e t' in
            let clauses' =
              List.map
                (fun (p, ss) ->
                  let fragment, p', venv' =
                    infer_pat_fragment tenv venv p t' in
                  let css, ss' =
                    List.split (List.map (infer_stmt tenv venv') ss) in
                  let wcss, ss' = List.split ss' in
                  CLet ([ Scheme (p.pattern_loc, [], fragment.vars,
                                  fragment.tconstraint,
                                  fragment.gamma) ],
                        conj css),
                  (wconj wcss, (p', ss')))
                clauses in
            let ccl, clauses' = List.split clauses' in
            let wcl, clauses' = List.split clauses' in
            ce ^ conj ccl,
            (wce @^ wconj wcl,
             make_stmt (S_case (e', clauses'))))
    | S_print (b, e) ->
        exists_aux (fun t' ->
            let ce, (wce, e') = infer_expr tenv venv e t' in
            ce, (wce, make_stmt (S_print (b, e'))))

let infer_action tenv venv act t =
  (* [t] can only bind the last expression if any of the sequence,
   * otherwise it should equal [unit]. *)
  let ss, e = act.action_stmts in
  let css, ss' = List.split (List.map (infer_stmt tenv venv) ss) in
  let wcss, ss' = List.split ss' in
  let ce, (wce, e') = match e with
      | None ->
          let u = typcon_variable tenv (std_type "unit") in
          (t =?= u) act.action_loc, (WC_true, None)
      | Some e ->
          let c, (wc, e') = infer_expr tenv venv e t in
          c, (wc, Some e') in
  conj css ^ ce,
  wconj wcss @^ wce,
  {action_stmts = (ss', e'); action_loc = act.action_loc}


(* The bit-alignment of the rule-element as an
   integral number of bits.
 *)
type cursor = int

let is_aligned cursor alignment =
  (* alignments should be byte-aligned *)
  assert (alignment mod 8 = 0);
  cursor mod alignment = 0

let check_aligned cursor alignment loc pos =
  (* alignments should be byte-aligned *)
  assert (alignment mod 8 = 0);
  let offset = cursor mod alignment in
  if   offset <> 0
  then let err = NotByteAligned (offset, alignment, pos) in
       raise (Error (loc, err))

(* local intra-rule inter-rule-element inference context *)
type ictx =
  {bound:        bool;
   in_map_views: bool}

(* [bound] tracks whether this rule_elem is under a binding.
    This affects the typing of the '|' choice operator:
      a=( ... (re | re') ... )
    requires [re] and [re'] to receive the same type, which does not
    apply to an unbound choice
      ... (re | re') ...
    where re and re' can receive different types.
 *)
(* [in_map_view] tracks whether this rule_elem is directly under a
    map_views construct.  This affects the typing of the A_in 'vector'
    assignment, which is legal only if it occurs in a non-terminal
    directly under map_views.
 *)
(* Since RE_named is a binding construct that is processed before the
   rule elements it scopes over in any sequence it occurs in, we
   employ constraint abstractions (or contexts) in the same way as
   they are used for binding type declarations in the spec.  Here
   however, we close the chain of constraint contexts for a sequence
   of rule elements with a unit (CTrue) after processing the sequence.
   For type declarations, the chain is closed with a unit at the end
   of the spec.
 *)
(* The input [cursor] is the alignment at the beginning of the
   rule-element, and the alignment at the end is returned.
 *)

let rec infer_rule_elem tenv venv ntd ctx cursor re t ictx
        : context
        * width_constraint
        * (crterm, varid, mod_qual) rule_elem
        * VEnv.t
        * cursor =
  let unit = CTrue re.rule_elem_loc in
  let pack_constraint c' =
    (fun c -> ctx (c' ^ c)) in
  let mk_regexp_type () =
    let byte = typcon_variable tenv (std_type "byte") in
    list (typcon_variable tenv) byte in
  let mk_aux_rule_elem re' =
    {rule_elem     = re';
     rule_elem_loc = re.rule_elem_loc;
     rule_elem_mod = re.rule_elem_mod;
     rule_elem_aux = t} in
  match re.rule_elem with
    | RE_regexp r ->
        check_aligned cursor 8 re.rule_elem_loc At_begin;
        let c, (wc, r') = infer_regexp tenv venv r t in
        pack_constraint c,
        wc,
        mk_aux_rule_elem (RE_regexp r'),
        venv,
        0
    | RE_scan scan ->
        check_aligned cursor 8 re.rule_elem_loc At_begin;
        (* Scans result in matched bytes, and hence are equivalent in
           type to regular expressions. *)
        let c = (t =?= mk_regexp_type ()) re.rule_elem_loc in
        pack_constraint c,
        WC_true,
        mk_aux_rule_elem (RE_scan scan),
        venv,
        0
    | RE_non_term (m, nid, None) ->
        let n = Location.value nid in
        assert (n <> "BitVector");
        check_aligned cursor 8 re.rule_elem_loc At_begin;

        (match lookup_non_term tenv (m, NName n) with
           | None ->
               raise (Error (Location.loc nid, UnknownNonTerminal nid))
           | Some ((inh, _), syn, _) ->
               (* Check if inherited attributes need to be specified. *)
               (match StringMap.choose_opt inh with
                  | None ->
                      let c = (t =?= syn) re.rule_elem_loc in
                      pack_constraint c,
                      WC_true,
                      mk_aux_rule_elem (RE_non_term (m, nid, None)),
                      venv,
                      0
                  | Some (id, _) ->
                      let loc = Location.loc nid in
                      raise (Error (loc, NTInheritedUnspecified (nid, id)))))
    | RE_non_term (m, cntid, Some attrs) ->
        let cntn = Location.value cntid in
        assert (cntn <> "BitVector");
        check_aligned cursor 8 re.rule_elem_loc At_begin;
        let cnti = match lookup_non_term tenv (m, NName cntn) with
            | None ->
                raise (Error (Location.loc cntid, UnknownNonTerminal cntid))
            | Some ((inh_typ, _), _, _) ->
                inh_typ in
        let pids, cs, wcs, attrs' =
          List.fold_left (fun (pids, cs, wcs, attrs') (pid, assign, e) ->
              let pn = Location.value pid in
              let pids = match StringMap.find_opt pn pids with
                  | Some repid ->
                      let loc = Location.loc pid in
                      raise (Error (loc, NTRepeatedBinding (cntid, pid, repid)))
                  | None ->
                      StringMap.add pn pid pids in
              let typ = match assign, StringMap.find_opt pn cnti with
                  | A_eq, Some (typ, _) ->
                      typ
                  | A_in, Some (typ, _) ->
                      if   ictx.in_map_views
                      then list (typcon_variable tenv) typ
                      else let loc = Location.loc pid in
                           let err =
                             NTIllegalMapAttributeAssignment (cntid, pid) in
                           raise (Error (loc, err))
                  | _, None ->
                      let loc = Location.loc pid in
                      raise (Error (loc, NTUnknownInheritedAttribute (cntid, pid))) in
              let c, (wc, e') = infer_expr tenv venv e typ in
              pids, c :: cs, wc :: wcs, (pid, assign, e') :: attrs'
            ) (StringMap.empty, [], [], []) attrs in
        StringMap.iter (fun pn _ ->
            if   not (StringMap.mem pn pids)
            then let loc = Location.loc cntid in
                 raise (Error (loc, NTInheritedUnspecified (cntid, pn)))
          ) cnti;
        pack_constraint (conj cs),
        wconj wcs,
        mk_aux_rule_elem (RE_non_term (m, cntid, Some attrs')),
        venv,
        0
    | RE_bitfield bf ->
        (* TODO: Support cross-module bitfield references. *)
        let m = infer_mod re.rule_elem_mod in
        let width = TypedAstUtils.lookup_bitfield_length tenv m bf in
        let cursor = cursor + width in
        (* The matched bits are converted into the bitfield record
           type. *)
        let bft = AstUtils.make_tname_id m bf in
        let bft = TypeConv.intern tenv bft in
        let c = (t =?= bft) re.rule_elem_loc in
        pack_constraint c,
        WC_true,
        mk_aux_rule_elem (RE_bitfield bf),
        venv,
        cursor
    | RE_bitvector w ->
        let width = Location.value w in
        (if   width <= 0
         then raise (Error (re.rule_elem_loc, InvalidBitvectorWidth width)));
        let cursor = cursor + width in
        let bvt = TypeConv.bitvector_n tenv width in
        let c = (t =?= bvt) re.rule_elem_loc in
        pack_constraint c,
        WC_true,
        mk_aux_rule_elem (RE_bitvector w),
        venv,
        cursor
    | RE_align a ->
        (* Alignments need to be a multiple of 8. *)
        let align = Location.value a in
        (if   align mod 8 <> 0
         then let err = InvalidAlignment a in
              raise (Error (Location.loc a, err)));
        (* Alignments matching 0 bits are currently forbidden. *)
        (if   cursor mod align = 0
         then raise (Error (re.rule_elem_loc, ZeroWidthAlignment)));
        let width = align - (cursor mod align) in
        let cursor' = cursor + width in
        assert (is_aligned cursor' align);
        let bvt = TypeConv.bitvector_n tenv width in
        let c = (t =?= bvt) re.rule_elem_loc in
        pack_constraint c,
        WC_true,
        mk_aux_rule_elem (RE_align a),
        venv,
        cursor'
    | RE_pad(a, _) ->
        (* Alignments need to be a multiple of 8.
           TODO: if padding literal is longer than alignment, we
           should warn about used bits, but probably not throw an
           error. *)
        let align = Location.value a in
        (if   align mod 8 <> 0
         then let err = InvalidAlignment a in
              raise (Error (Location.loc a, err)));
        (* Alignments matching 0 bits are currently forbidden. *)
        (if   cursor mod align = 0
         then raise (Error (re.rule_elem_loc, ZeroWidthAlignment)));
        let width = align - (cursor mod align) in
        let cursor' = cursor + width in
        assert (is_aligned cursor' align);
        let bvt = TypeConv.bitvector_n tenv width in
        let c = (t =?= bvt) re.rule_elem_loc in
        pack_constraint c,
        WC_true,
        mk_aux_rule_elem (RE_align a),
        venv,
        cursor'
    | RE_constraint e ->
        let b = typcon_variable tenv (std_type "bool") in
        let c, (wc, e') = infer_expr tenv venv e b in
        let c = (t =?= b) re.rule_elem_loc ^ c in
        pack_constraint c,
        wc,
        mk_aux_rule_elem (RE_constraint e'),
        venv,
        cursor
    | RE_action a ->
        let c, wc, a' = infer_action tenv venv a t in
        pack_constraint c,
        wc,
        mk_aux_rule_elem (RE_action a'),
        venv,
        cursor
    | RE_named (id, re') ->
        (* [id] is bound in the environment when typing [re'] *)
        let idloc = Location.loc id in
        let id' = var_name id in
        let v, venv' = VEnv.add venv id in
        (* re' needs to be typed under a binding *)
        let ictx = {bound = true; in_map_views = false} in
        let ctx', wc, re'', _, cursor' =
          infer_rule_elem tenv venv ntd (fun c -> c) cursor re' t ictx in
        (fun c ->
          ctx (CLet ([Scheme (re.rule_elem_loc, [], [],
                              CTrue re.rule_elem_loc,
                              StringMap.singleton id' (t, idloc))],
                     c ^ ctx' unit))),
        wc,
        mk_aux_rule_elem (RE_named (v, re'')),
        venv',
        cursor'

    | RE_seq rels | RE_seq_flat rels ->
        (* A sequence has a tuple type formed from the individual rule
           elements, unless they are all regexps, in which case they
           are flattened. *)
        let m = infer_mod re.rule_elem_mod in
        let is_regexp =
          List.for_all (TypedAstUtils.is_regexp_elem tenv m) rels in
        let qs, m = variable_list Flexible rels in
        let ictx = {ictx with in_map_views = false} in
        let ctx', wcs', rels', _, cursor' =
          List.fold_left (fun (ctx', wcs', rels', venv', cursor') (re, t') ->
              let ctx', wc', re', venv', cursor' =
                infer_rule_elem tenv venv' ntd ctx' cursor' re t' ictx in
              ctx', wc' :: wcs', re' :: rels', venv', cursor'
            ) ((fun c -> c), [], [], venv, cursor) m in
        let typ =
          if   is_regexp
          then mk_regexp_type ()
          else tuple (typcon_variable tenv) (snd (List.split m)) in
        let c =
          ex ~pos:re.rule_elem_loc qs
            ((t =?= typ) re.rule_elem_loc ^ ctx' unit) in
        let rels' = List.rev rels' in
        pack_constraint c,
        wconj wcs',
        mk_aux_rule_elem
          (if is_regexp then RE_seq_flat rels' else RE_seq rels'),
        venv,
        cursor'

    | RE_choice rels
         when List.for_all (TypedAstUtils.is_regexp_elem tenv
                              (infer_mod re.rule_elem_mod)) rels ->
        (* Non-sequence combinators can only start and end at
           bit-aligned positions. *)
        check_aligned cursor 8 re.rule_elem_loc At_begin;
        (* If the sequence is composed purely of regexps, flatten into
           a single byte list, after ensuring each element is
           well-typed. *)
        let qs, m = variable_list Flexible rels in
        let ictx = {ictx with in_map_views = false} in
        let ctx', wcs', rels', _ =
          List.fold_left (fun (ctx', wcs', rels', venv') (re, t') ->
              let ctx', wc', re', venv', cursor' =
                infer_rule_elem tenv venv' ntd ctx' 0 re t' ictx in
              check_aligned cursor' 8 re.rule_elem_loc At_end;
              ctx', wc' :: wcs', re' :: rels', venv'
            ) ((fun c -> c), [], [], venv) m in
        let typ = mk_regexp_type () in
        let c =
          ex ~pos:re.rule_elem_loc qs
            ((t =?= typ) re.rule_elem_loc ^ ctx' unit) in
        pack_constraint c,
        wconj wcs',
        mk_aux_rule_elem (RE_choice (List.rev rels')),
        venv,
        0

    | RE_choice rels ->
        (* Non-sequence combinators can only start and end at
           bit-aligned positions. *)
        check_aligned cursor 8 re.rule_elem_loc At_begin;
        let ictx = {ictx with in_map_views = false} in
        if   ictx.bound
        then (* Each choice should have the same type [t]. *)
             let ctx', wcs', rels', _ =
               List.fold_left (fun (ctx', wcs', rels', venv') re ->
                   let ctx', wc', re', venv', cursor' =
                     infer_rule_elem tenv venv' ntd ctx' 0 re t ictx in
                   check_aligned cursor' 8 re.rule_elem_loc At_end;
                   ctx', wc' :: wcs', re' :: rels', venv'
                 ) ((fun c -> c), [], [], venv) rels in
             pack_constraint (ctx' unit),
             wconj wcs',
             mk_aux_rule_elem (RE_choice (List.rev rels')),
             venv,
             0
        else (* Each choice can receive a different type, and [t] is
                unconstrained *)
             let qs, m = variable_list Flexible rels in
             let ctx', wcs', rels', _ =
               List.fold_left (fun (ctx', wcs', rels', venv') (re, t') ->
                   let ctx', wc', re', venv', cursor' =
                     infer_rule_elem tenv venv' ntd ctx' 0 re t' ictx in
                   check_aligned cursor' 8 re.rule_elem_loc At_end;
                   ctx', wc' :: wcs', re' :: rels', venv'
                 ) ((fun c -> c), [], [], venv) m in
             let c =
               ex ~pos:re.rule_elem_loc qs (ctx' unit) in
             pack_constraint c,
             wconj wcs',
             mk_aux_rule_elem (RE_choice (List.rev rels')),
             venv,
             0

    | RE_star (re', None) ->
        (* Non-sequence combinators can only start and end at
           bit-aligned positions. *)
        check_aligned cursor 8 re.rule_elem_loc At_begin;
        (* [re] has a type [list t'] where [t'] is the type of [re'],
           unless [re'] is a regexp, in which case it is flattened. *)
        let m = infer_mod re.rule_elem_mod in
        let is_regexp = TypedAstUtils.is_regexp_elem tenv m re' in
        let q  = variable Flexible () in
        let t' = CoreAlgebra.TVariable q in
        let ictx = {ictx with in_map_views = false} in
        let ctx', wc', re'', _, cursor' =
          infer_rule_elem tenv venv ntd (fun c -> c) 0 re' t' ictx in
        check_aligned cursor' 8 re.rule_elem_loc At_end;
        let typ = if   is_regexp
                  then mk_regexp_type ()
                  else list (typcon_variable tenv) t' in
        let c =
          ex ~pos:re.rule_elem_loc [q]
            ((t =?= typ) re.rule_elem_loc ^ ctx' unit) in
        pack_constraint c,
        wc',
        mk_aux_rule_elem (RE_star (re'', None)),
        venv,
        0
    | RE_star (re', Some e) ->
        (* Non-sequence combinators can only start and end at
           bit-aligned positions. *)
        check_aligned cursor 8 re.rule_elem_loc At_begin;
        (* [re] has a type [list t'] where [t'] is the type of [re']
           (unless [re'] is a regexp) and [e] has type unsigned *)
        let m = infer_mod re.rule_elem_mod in
        let is_regexp = TypedAstUtils.is_regexp_elem tenv m re' in
        let int = typcon_variable tenv (std_type "usize") in
        let q  = variable Flexible () in
        let t' = CoreAlgebra.TVariable q in
        let ictx = {ictx with in_map_views = false} in
        let ctx', wc'', re'', _, cursor' =
          infer_rule_elem tenv venv ntd (fun c -> c) 0 re' t' ictx in
        check_aligned cursor' 8 re.rule_elem_loc At_end;
        let typ = if   is_regexp
                  then mk_regexp_type ()
                  else list (typcon_variable tenv) t' in
        let ce, (wce, e') = infer_expr tenv venv e int in
        let c =
          ex ~pos:re.rule_elem_loc [q]
            ((t =?= typ) re.rule_elem_loc ^ ce ^ ctx' unit) in
        pack_constraint c,
        wc'' @^ wce,
        mk_aux_rule_elem (RE_star (re'', Some e')),
        venv,
        0

    | RE_opt re' ->
        (* Non-sequence combinators can only start and end at
           bit-aligned positions. *)
        check_aligned cursor 8 re.rule_elem_loc At_begin;
        (* [re] has a type [option t'] where [t'] is the type of [re']
           (unless [re'] is a regexp) *)
        let m = infer_mod re.rule_elem_mod in
        let is_regexp = TypedAstUtils.is_regexp_elem tenv m re' in
        let q  = variable Flexible () in
        let t' = CoreAlgebra.TVariable q in
        let ictx = {ictx with in_map_views = false} in
        let ctx', wc', re'', _, cursor' =
          infer_rule_elem tenv venv ntd (fun c -> c) 0 re' t' ictx in
        check_aligned cursor' 8 re.rule_elem_loc At_end;
        let typ = if   is_regexp
                  then mk_regexp_type ()
                  else option (typcon_variable tenv) t' in
        let c =
          ex ~pos:re.rule_elem_loc [q]
            ((t =?= typ) re.rule_elem_loc ^ ctx' unit) in
        pack_constraint c,
        wc',
        mk_aux_rule_elem (RE_opt re''),
        venv,
        0

    | RE_suspend_resume (n, args)
         when Location.value n = "require_remaining"
              && List.length args = 2 ->
        let v = List.nth args 0 in
        let e = List.nth args 1 in
        (* Suspensions can only occur at bit-aligned positions. *)
        check_aligned cursor 8 re.rule_elem_loc At_begin;
        let vt = typcon_variable tenv (std_type "view") in
        let et = typcon_variable tenv (std_type "usize") in
        let cv, (wv, v') = infer_expr tenv venv v vt in
        let ce, (we, e') = infer_expr tenv venv e et in
        (* This behaves like a boolean constraint. *)
        let bt = typcon_variable tenv (std_type "bool") in
        let cr = (t =?= bt) re.rule_elem_loc in
        pack_constraint (conj [cv; ce; cr]),
        wconj [wv; we],
        mk_aux_rule_elem (RE_suspend_resume (n, [v'; e'])),
        venv,
        0

    | RE_suspend_resume (n, args)
         when Location.value n = "require_remaining" ->
        let err = ConstraintArity (Location.value n, 2, List.length args) in
        raise (Error (Location.loc n, err))

    | RE_suspend_resume (n, _) ->
        let err = UnknownSuspendResumeConstraint (Location.value n) in
        raise (Error (Location.loc n, err))

    | RE_epsilon ->
        let u = typcon_variable tenv (std_type "unit") in
        let c = (t =?= u) re.rule_elem_loc in
        pack_constraint c,
        WC_true,
        mk_aux_rule_elem RE_epsilon,
        venv,
        cursor

    | RE_set_view vu ->
        (* Non-sequence combinators can only start and end at
           bit-aligned positions. *)
        check_aligned cursor 8 re.rule_elem_loc At_begin;
        (* [vu] should have type [view] *)
        let view = typcon_variable tenv (std_type "view") in
        let cb, (wcb, vu') = infer_expr tenv venv vu view in
        pack_constraint cb,
        wcb,
        mk_aux_rule_elem (RE_set_view vu'),
        venv,
        0
    | RE_at_pos (e, re') ->
        (* Non-sequence combinators can only start and end at
           bit-aligned positions. *)
        check_aligned cursor 8 re.rule_elem_loc At_begin;
        (* [pos] needs to be unsigned and [re'] should have type [t] *)
        let int = typcon_variable tenv (std_type "usize") in
        let ce, (wce, e') = infer_expr tenv venv e int in
        let ictx = {ictx with in_map_views = false} in
        let ctx', wc, re'', _, cursor' =
          infer_rule_elem tenv venv ntd (fun c -> c) 0 re' t ictx in
        check_aligned cursor' 8 re.rule_elem_loc At_end;
        pack_constraint (ce ^ ctx' unit),
        wce @^ wc,
        mk_aux_rule_elem (RE_at_pos (e', re'')),
        venv,
        0
    | RE_at_view (vu, re') ->
        (* Non-sequence combinators can only start and end at
           bit-aligned positions. *)
        check_aligned cursor 8 re.rule_elem_loc At_begin;
        (* [vu] should have type [view] and [re'] should have type [t] *)
        let view = typcon_variable tenv (std_type "view") in
        let cb, (wcb, vu') = infer_expr tenv venv vu view in
        let ictx = {ictx with in_map_views = false} in
        let ctx', wc', re'', _, cursor' =
          infer_rule_elem tenv venv ntd (fun c -> c) 0 re' t ictx in
        check_aligned cursor' 8 re.rule_elem_loc At_end;
        pack_constraint (cb ^ ctx' unit),
        wcb @^ wc',
        mk_aux_rule_elem (RE_at_view (vu', re'')),
        venv,
        0
    | RE_map_views (vus, re') ->
        (* Non-sequence combinators can only start and end at
           bit-aligned positions. *)
        check_aligned cursor 8 re.rule_elem_loc At_begin;
        (* [vus] should have type [list view] and [re] should have
         * type [list t'] where [t'] is the type of [re'] *)
        let view = typcon_variable tenv (std_type "view") in
        let views = list (typcon_variable tenv) view in
        let cb, (wcb, vus') = infer_expr tenv venv vus views in
        let q  = variable Flexible () in
        let t' = CoreAlgebra.TVariable q in
        let ictx = {ictx with in_map_views = true} in
        let ctx', wc', re'', _, cursor' =
          infer_rule_elem tenv venv ntd (fun c -> c) 0 re' t' ictx in
        check_aligned cursor' 8 re.rule_elem_loc At_end;
        let result = list (typcon_variable tenv) t' in
        let c =
          ex ~pos:re.rule_elem_loc [q]
            (cb ^ (t =?= result) re.rule_elem_loc ^ ctx' unit) in
        pack_constraint c,
        wcb @^ wc',
        mk_aux_rule_elem (RE_map_views (vus', re'')),
        venv,
        0

let infer_non_term_rule tenv venv ntd rule pids =
  (* add temporaries to local bindings *)
  let _pids, bindings, wcs, temps', venv' =
    List.fold_left (fun (pids, fragment, wcs, temps, venv') (pid, typ, exp) ->
        let pn, ploc = var_name pid, Location.loc pid in
        let pids =
          let pid = ident_of_var pid in
          match StringMap.find_opt pn pids with
            | Some repid ->
                let loc = Location.loc pid in
                raise (Error (loc, NTRepeatedBinding (ntd.non_term_name, pid, repid)))
            | None ->
                StringMap.add pn pid pids in
        let ityp = intern_expanded_type tenv typ in
        let v = variable Flexible () in
        let cexp, (wce, exp') = infer_expr tenv venv' exp ityp in
        let pid', venv' = VEnv.add venv' pid in
        let temp = pid', typ, exp' in
        pids,
        {gamma = StringMap.add pn (CoreAlgebra.TVariable v, ploc)
                   fragment.gamma;
         tconstraint = (CoreAlgebra.TVariable v =?= ityp) ploc
                       ^ cexp
                       ^ fragment.tconstraint;
         vars = v :: fragment.vars},
        wce :: wcs,
        temp :: temps,
        venv'
      ) (pids, empty_fragment, [], [], venv) rule.rule_temps in
  let init_ictx = {bound = false; in_map_views = false} in
  let qs, ctx, wcs, rhs', _, cursor' =
    List.fold_left (fun (qs, ctx, wcs, rhs', venv', cursor) re ->
        let q  = variable Flexible () in
        let t' = CoreAlgebra.TVariable q in
        let ctx', wc', re', venv', cursor' =
          infer_rule_elem tenv venv' ntd ctx cursor re t' init_ictx in
        q :: qs, ctx', wc' :: wcs, re' :: rhs', venv', cursor'
      ) ([], (fun c -> c), wcs, [], venv', 0) rule.rule_rhs in
  (* Ensure that there is at least one rule element in the rule. *)
  if   List.length rhs' = 0
  then raise (Error (rule.rule_loc, NTEmptyRule ntd.non_term_name));
  check_aligned cursor' 8 rule.rule_loc At_end;
  CLet ([ Scheme (rule.rule_loc, [],
                  bindings.vars,
                  bindings.tconstraint,
                  bindings.gamma) ],
        (ex ~pos:rule.rule_loc qs (ctx (CTrue rule.rule_loc)))),
  (wconj wcs,
   {rule_rhs = List.rev rhs'; rule_temps = List.rev temps'; rule_loc = rule.rule_loc})

let infer_non_term tenv venv ntd =
  let m = infer_mod ntd.non_term_mod in
  let ntid = NName (Location.value ntd.non_term_name) in
  let inh_attr_map, inh_attrs = match lookup_non_term tenv (m, ntid) with
      | None ->
          (* the type definition is processed in the previous typing
             pass and should already be present *)
          assert false
      | Some (i, _, _) ->
          i in

  (* If there are any initializers for the synthesized attributes,
   * collect their typing constraints.
   *)
  let csyn_attrs, wcsyn_attrs, non_term_syn_attrs =
    match ntd.non_term_syn_attrs with
      | ALT_type t ->
          [], [], ALT_type t
      | ALT_decls d ->
          let c, wc, d' =
            List.fold_left (fun (cs, wcs, ds) (pid, typ, _, exp) ->
                let ityp = intern_expanded_type tenv typ in
                match exp with
                  | None ->
                      cs, wcs, (pid, typ, ityp, None) :: ds
                  | Some e ->
                      let c, (wc, e') = infer_expr tenv venv e ityp in
                      c :: cs, wc :: wcs, (pid, typ, ityp, Some e') :: ds
              ) ([], [], []) d in
          c, wc, ALT_decls (List.rev d') in
  (* compute the local bindings for each rule: this includes any
   * name for the non-terminal itself, along with the bindings
   * for the inherited attributes.
   *)
  let pids, bindings, venv', nt_varname = match ntd.non_term_varname with
      | None ->
          StringMap.empty, empty_fragment, venv, None
      | Some n ->
          let nloc = Location.loc n in
          let ntt  = match lookup_non_term_type tenv (m, ntid) with
              | None   -> assert false
              | Some t -> t in
          let v = variable Flexible () in
          let nt_varname, venv' = VEnv.add venv n in
          StringMap.singleton (var_name n) (ident_of_var n),
          {gamma = StringMap.singleton (var_name n)
                     (CoreAlgebra.TVariable v, nloc);
           tconstraint = (CoreAlgebra.TVariable v =?= ntt) nloc;
           vars = [ v ]},
          venv',
          Some nt_varname in
  let pids, bindings =
    List.fold_left (fun (pids, fragment) (pn, (ityp, ploc)) ->
        let pid = Location.mk_loc_val pn ploc in
        let pids =
          match StringMap.find_opt pn pids with
            | Some repid ->
                let loc = Location.loc pid in
                raise (Error (loc, NTRepeatedBinding (ntd.non_term_name, pid, repid)))
            | None ->
                StringMap.add pn pid pids in
        let v = variable Flexible () in
        pids,
        {gamma = StringMap.add pn (CoreAlgebra.TVariable v, ploc)
                   fragment.gamma;
         tconstraint = (CoreAlgebra.TVariable v =?= ityp) ploc
                       ^ fragment.tconstraint;
         vars = v :: fragment.vars}
      ) (pids, bindings) (StringMap.bindings inh_attr_map) in
  let venv' =
    List.fold_left (fun venv' (v', _, _) ->
        VEnv.extend venv' (var_name v') v'
      ) venv' inh_attrs in
  let crules' = List.map
                 (fun r -> infer_non_term_rule tenv venv' ntd r pids)
                 ntd.non_term_rules in
  (* Ensure that there is at least one rule specified. *)
  (if   List.length crules' = 0
   then let loc = Location.loc ntd.non_term_name in
        raise (Error (loc, NTNoRules ntd.non_term_name)));
  let cs, rules' = List.split crules' in
  let wcs, rules' = List.split rules' in
  let cprod =
    CLet ([ Scheme (ntd.non_term_loc, [],
                    bindings.vars,
                    bindings.tconstraint,
                    bindings.gamma) ],
          conj cs) in
  (conj csyn_attrs) ^ cprod,
  wconj wcsyn_attrs @^ wconj wcs,
  {non_term_name      = ntd.non_term_name;
   non_term_varname   = nt_varname;
   non_term_inh_attrs = inh_attrs;
   non_term_syn_attrs = non_term_syn_attrs;
   non_term_rules     = rules';
   non_term_mod       = ntd.non_term_mod;
   non_term_loc       = ntd.non_term_loc}

(** Initialize the typing environment with the builtin types and
    constants. *)
let init_env () =
  let mk_variable = (fun ?name () -> variable Rigid ?name:name ()) in
  let mk_type_ent (o, (arity, _, ds)) =
    let ft = std_tname o in
    ft, (arity,
        CoreAlgebra.TVariable (mk_variable ?name:(Some ft) ()),
        ds) in
  let init_builtin_types types =
    List.rev (
        Array.fold_left
          (fun acu entry -> mk_type_ent entry :: acu)
          [] types) in
  let builtin_types = init_builtin_types builtin_types in

  (* bitvector widths are constructed dynamically depending on the max
     size seen in the spec *)
  let builtin_bitwidths =
    let rec recur i acc =
      if   i = 0
      then acc
      else let ent = mk_type_ent (mk_builtin_bitwidth i) in
           recur (i - 1) (ent :: acc) in
    recur !max_width [] in
  let builtin_types = builtin_bitwidths @ builtin_types in

  (* Add the builtin data constructors into the environment.  The
     builtins currently only use variant algebraic types. *)
  let init_ds (_, TName adt_name) env_info ds =
    let adt_id = Location.mk_ghost adt_name in
    let (_tenv, dcs, _lrqs, _let_env) as env_info =
      List.fold_left
        (fun env_info (DName d, qs, ty) ->
          let qs = List.map (fun (TName q) -> Location.mk_ghost q) qs in
          let d = Location.mk_ghost d in
          intern_data_constructor true AstUtils.stdlib adt_id qs env_info (d, Some ty)
        ) env_info ds in
    (dcs, env_info) in

  (* Compute the scheme of a builtin constant. *)
  let intern_const tenv qs typ =
    let rqs, rtenv = fresh_unnamed_rigid_vars Location.ghost_loc tenv qs in
    let tenv' = add_type_variables rtenv tenv in
    let ityp = intern_expanded_type tenv' typ in
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
    if   List.length dcs > 0
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
    Array.fold_left (fun (lrqs, let_env) (VName c, qs, typ) ->
        let qs = List.map (fun q -> stdlib, q) qs in
        let rqs, ityp = intern_const init_tenv qs typ in
        rqs @ lrqs,
        StringMap.add c (ityp, Location.ghost_loc) let_env
      ) (lrqs, let_env) builtin_ops in

  (* Update with the builtin variables. *)
  let lrqs, let_env, init_venv =
    let make_var s =
      Location.mk_loc_val (s, ()) Location.ghost_loc in
    Array.fold_left (fun (lrqs, let_env, venv) (VName c, qs, typ) ->
        let qs = List.map (fun q -> stdlib, q) qs in
        let rqs, ityp = intern_const init_tenv qs typ in
        rqs @ lrqs,
        StringMap.add c (ityp, Location.ghost_loc) let_env,
        snd (VEnv.add venv (make_var c))
      ) (lrqs, let_env, VEnv.empty) builtin_values in

  (* Update with the builtin module values. *)
  let init_tenv, lrqs, let_env =
    let builtin_loc = Location.ghost_loc in
    List.fold_left (fun (tenv, lrqs, let_env) minfo ->
        (List.fold_left
           (fun (tenv, lrqs, let_env)
                ((VName vid) as v, qs, typ) ->
             let qs = List.map (fun q -> stdlib, q) qs in
             (* Encode the item name as it appears in the source. *)
             let m  = Modul minfo.mod_name in
             let id = Printf.sprintf "%s%s"
                        (AstUtils.mk_modprefix m) vid in
             let rqs, ityp = intern_const tenv qs typ in
             add_value tenv builtin_loc (m, v) (rqs, ityp),
             rqs @ lrqs,
             StringMap.add id (ityp, builtin_loc) let_env
           ) (tenv, lrqs, let_env) minfo.mod_values)
      ) (init_tenv, lrqs, let_env) builtin_modules in

  (* Update with the builtin non-terminals.  These are implemented
     with primitive builtin types. *)
  let init_tenv =
    Array.fold_left (fun tenv ((NName n) as nt, inh_attrs, typ) ->
        let gloc = Location.ghost_loc in
        let nid = Location.mk_ghost n in
        let typ = intern_expanded_type tenv typ in
        (* builtin non-terminals are non-record types *)
        let syn_typ = NTT_type (typ, None) in
        let inh_typ = infer_non_term_attrs tenv nid inh_attrs in
        let ntt = (inh_typ, syn_typ) in
        add_non_terminal tenv gloc (stdlib, nt) ntt
      ) init_tenv builtin_non_terms in

  (* Extract the variables bound to the type constructors. *)
  let vs =
    fold_type_info (fun _n (_, v, _) vs -> v :: vs) [] init_tenv in

  (* The initial environment is implemented as a constraint context. *)
  init_tenv,
  init_venv,
  (fun c ->
    CLet ([ Scheme
              (Location.ghost_loc, vs, [],
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
        | None   -> (
          let tr = td.type_decl_body in
          match tr.type_rep with
            | TR_defn _ -> Some td
            | _         -> None
        )
    ) None tds


let process_decorator _tenv _venv (fd: (unit, unit, mod_qual) format_decl)
    : (unit, unit, mod_qual) format_decl =
  (* Currently, the only supported decorator is 'whitespace'.  If
     specified, it should name a valid non-terminal. *)
  let m = infer_mod fd.format_decl.non_term_mod in
  match Format_decorators.get_whitespace_nonterm m fd.format_deco with
    | None ->
        fd
    | Some ws ->
        let ntd = fd.format_decl in
        {fd with
          format_decl = Format_decorators.fixup_for_whitespace ntd ws}

let infer_spec tenv venv spec =
  (* First pass: process the expression language, and the
     type-definitions for the non-terminals, and collect their
     annotated versions *)
  let tenv, ctxt, wc, decls, venv =
    List.fold_left (fun (tenv, ctxt, wc, decls, venv) decl ->
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
                     if   List.length tds > 1
                     then let id = td.type_decl_ident in
                          let err =
                            PotentiallyRecursiveTypeAbbreviation id in
                          raise (Error (Location.loc id, err))
                     else let tenv' = infer_type_abbrev tenv td in
                          tenv', ctxt, wc, decls', venv
                 | None ->
                     let tenv', ctxt =
                       infer_type_decls tenv ctxt tdsloc tds in
                     tenv', ctxt, wc, decls', venv
              )
          | Decl_const const ->
              let m = const.const_defn_mod in
              let venv = VEnv.in_module venv m in
              let tenv, c, wc', const' =
                infer_const_defn tenv venv ctxt const in
              (* bind the const name *)
              let cid = const'.const_defn_ident in
              let venv' = VEnv.extend venv (var_name cid) cid in
              tenv, c, wc @^ wc', Decl_const const' :: decls, venv'
          | Decl_fun f ->
              let venv = VEnv.in_module venv f.fun_defn_mod in
              let tenv, c, wc', f' = infer_fun_defn tenv venv ctxt f in
              (* bind the function names *)
              let fid = f'.fun_defn_ident in
              let venv' = VEnv.extend venv (var_name fid) fid in
              tenv, c, wc @^ wc', Decl_fun f' :: decls, venv'
          | Decl_recfuns r ->
              let tenv, c, wc', r' = infer_recfun_defns tenv venv ctxt r in
              let venv' = List.fold_left (fun venv f' ->
                              let venv = VEnv.in_module venv f'.fun_defn_mod in
                              let fid = f'.fun_defn_ident in
                              VEnv.extend venv (var_name fid) fid
                            ) venv r'.recfuns in
              tenv, c, wc @^ wc', Decl_recfuns r' :: decls, venv'
          | Decl_foreign fs ->
              let tenv, venv', c, fs' =
                List.fold_left (fun (tenv, venv, c, fs') f ->
                    let venv = VEnv.in_module venv f.ffi_decl_mod in
                    let tenv, c, f' = infer_ffi_decl tenv venv c f in
                    (* bind the function name *)
                    let fid = f'.ffi_decl_ident in
                    let venv' = VEnv.extend venv (var_name fid) fid in
                    tenv, venv', c, f' :: fs'
                  ) (tenv, venv, ctxt, []) fs in
              tenv, c, wc, Decl_foreign (List.rev fs') :: decls, venv'
          | Decl_format f ->
              let tenv, ctxt =
                List.fold_left (fun (te, c) fd ->
                    let nt = fd.format_decl in
                    let m  = nt.non_term_mod in
                    let m  = infer_mod m in
                    Format_decorators.check_decorator m fd.format_deco;
                    let ntd = fd.format_decl in
                    infer_non_term_type te c ntd
                  ) (tenv, ctxt) f.format_decls in
              (* Annotate the grammar in the next pass *)
              tenv, ctxt, wc, decls, venv
      ) (tenv, (fun c -> c), WC_true, [], venv) spec.decls in

  (* Second pass: process the grammar spec comprising the rules for
     each non-terminal.  If any decorators need processing, those are
     handled here.
   *)
  let c', wc', decls =
    List.fold_left (fun (c, wc, decls) d ->
        match d with
          | Decl_format f ->
              let c, wc, fds' =
                List.fold_left (fun (c, wc, fds') fd ->
                    (* Since non-terminals can be specified within
                       decorators, it is important to type-check their
                       use in decorators.  A decorator can potentially
                       transform the untyped rules for a non-terminal,
                       resulting in new or different type-constraints
                       being generated. *)
                    let fd   = process_decorator tenv venv fd in
                    let ntd  = fd.format_decl in
                    let venv = VEnv.in_module venv ntd.non_term_mod in
                    let c', wc', ntd' = infer_non_term tenv venv ntd in
                    let fd' = {format_decl     = ntd';
                               format_deco     = fd.format_deco;
                               format_decl_loc = fd.format_decl_loc} in
                    c ^ c', wc @^ wc', fd' :: fds'
                  ) (c, wc, []) f.format_decls in
              let f' = {format_decls = List.rev fds';
                        format_loc   = f.format_loc} in
              c, wc, Decl_format f' :: decls
          | _ ->
              c, wc, decls
      ) ((CTrue Location.ghost_loc), wc, decls) spec.decls in

  let ctxt = (fun c -> ctxt (c' ^ c)) in
  tenv, ctxt, wc', {decls = List.rev decls}

let generate_constraint (tenv, venv, c) spec =
  let tenv', c', wc, spec' = infer_spec tenv venv spec in
  c (c' (CDump Location.ghost_loc)), wc, tenv', spec'

let typed_auxp
    : (MultiEquation.crterm, varid, mod_qual) AstPrinter.auxp =
  AstPrinter.mk_auxp_typed TypeConstraintPrinter.print_crterm
