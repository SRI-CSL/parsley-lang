module A  = Ast
module AU = Ast_utils
module TA = Typed_ast
module TU = Typing_utils
module L  = Location
module DG = Depgraph

module StringMap = AU.StringMap

(* nodes in dependency graph *)
type typeof_dep =
  | Tydep_nterm of A.path
  | Tydep_nterm_attr of A.path * A.ident

let nterm_of_dep = function
  | Tydep_nterm p -> p
  | Tydep_nterm_attr (p, _) -> p

let path_of_dep = function
  | Tydep_nterm p -> p
  | Tydep_nterm_attr (p, a) -> p @ [a]

let loc_of_dep d =
    AU.path_loc (nterm_of_dep d)

let str_of_dep d =
  AU.str_of_path (path_of_dep d)

type type_error =
  | Nonunique_type_var of A.tvar * L.t
  | Nonunique_type_defn of A.path * L.t
  | Nonunique_variant_constr of A.ident * L.t
  | Nonunique_fun_param of A.ident * L.t
  | Unknown_type_variable of A.tvar
  | Unknown_type_constructor of A.path
  | Unknown_non_terminal of A.path
  | Undefined_attribute of (* attr *) A.ident * (* non-terminal *) A.path
  | Invalid_path_attribute of (* attr *) A.ident * (* non-terminal *) A.path
  | Predefined_type of A.path
  | Incorrect_tycon_arity of A.path * (* expected *) int * (* found *) int
  | Cyclic_typeof_dependency of typeof_dep list
  | Undefined_path of A.path

exception Error of type_error * L.t

let error_string = function
  | Nonunique_type_var (tv, l) ->
        Printf.sprintf "non-unique type variable %s (previously defined on %s)"
                       (L.value tv) (L.str_of_file_loc l)
  | Nonunique_type_defn (p, l) ->
        Printf.sprintf "re-definition of type %s (previously defined at %s)"
                       (Ast_utils.str_of_path p) (L.str_of_loc l)
  | Nonunique_variant_constr (c, l) ->
        Printf.sprintf "re-definition of constructor %s (previously defined at %s)"
                       (L.value c) (L.str_of_loc l)
  | Nonunique_fun_param (p, l) ->
        Printf.sprintf "non-unique function parameter %s (previously defined on %s)"
                       (L.value p) (L.str_of_file_loc l)
  | Unknown_type_variable tv ->
        Printf.sprintf "unknown type variable %s"
                       (L.value tv)
  | Unknown_type_constructor p ->
        Printf.sprintf "unknown type constructor %s"
                       (Ast_utils.str_of_path p)
  | Unknown_non_terminal p ->
        Printf.sprintf "unknown non-terminal %s"
                       (Ast_utils.str_of_path p)
  | Undefined_attribute (a, nt) ->
        Printf.sprintf "no definition available for attribute %s of non-terminal %s"
                       (L.value a) (Ast_utils.str_of_path nt)
  | Invalid_path_attribute (a, nt) ->
        Printf.sprintf "attribute %s of non-terminal %s does not resolve to a non-terminal"
                       (L.value a) (Ast_utils.str_of_path nt)
  | Predefined_type p ->
        Printf.sprintf "cannot re-define predefined type %s"
                       (Ast_utils.str_of_path p)
  | Incorrect_tycon_arity (p, exp, fnd) ->
        Printf.sprintf "%d args expected for %s, found %d"
                       exp (Ast_utils.str_of_path p) fnd
  | Cyclic_typeof_dependency c ->
        "cyclic typeof dependency detected:"
        ^ (String.concat " -> " (List.map str_of_dep c))
  | Undefined_path p ->
        Printf.sprintf "undefined path %s" (AU.str_of_path p)

let type_error e loc =
  raise (Error (e, loc))

(* the well-typed signature for a function, without the body *)
type fun_sig =
    { fun_sig_ident: Ast.ident;
      fun_sig_tvars: TA.kind TU.Tvar.t list; (* universal tvars *)
      fun_sig_params: TA.param_decl list;
      fun_sig_res_type: TA.type_expr;
      fun_sig_loc: Location.t }

(* the type of a non-terminal, without the grammar rules *)
type nterm_type =
    { nterm_name: Ast.path;
      nterm_inh_attrs: TA.param_decl list;
      nterm_syn_attrs: TA.param_decl list;
      nterm_loc: Location.t }

module Ctx = struct
  type typing_ctx_entry =
    (* predefined base types with arities *)
    | CE_predefined_type of A.path * int
    (* universal type variable *)
    | CE_tvar of TA.kind TU.Tvar.t
    (* possibly typed program variable *)
    | CE_pvar of TA.var TU.Tvar.t option
    (* user type definition *)
    | CE_type_defn of A.path * TA.type_defn
    (* user function signature *)
    | CE_fun_sig of A.path * fun_sig
    (* non-term forward declaration *)
    | CE_non_term_decl of A.ident
    (* non-term definition *)
    | CE_non_term_type of nterm_type
    (* type definition variable: used for recursive types *)
    | CE_type_defn_var of A.path * int

  type t = {
    (* The variable context is a simple linear LIFO list containing
     * both type and program variables, with newer entries at the front
     * of the list.
     *)
    t_idents: typing_ctx_entry list;

    (* To ensure global uniqueness of value constructors in variants,
     * we map their names to the place where they were first
     * defined.  This implies OCaml-like global variant namespaces.
     * The alternative is a per-variant namespace as in Rust,
     * which will require syntax support.
     *)
    t_var_constrs: L.t StringMap.t;
  }

  let init () : t =
    (* populate with predefined base types *)
    let mk_predef_loc id =
      L.mk_loc_val id (L.make_ghost_loc ()) in
    let predef_types =
      [ "bool", 0; "int", 0; "u8", 0; "i64", 0; "double", 0;
        "string", 0
      ] in
    let mk_predef_ent (nm, arity) =
      CE_predefined_type ([mk_predef_loc nm], arity) in
    { t_idents = List.map mk_predef_ent predef_types;
      t_var_constrs = StringMap.empty }

  (* new identifiers go to the front of the list, so that they are
   * the first to be found on lookup.
   *)
  let extend_idents ctx (ents: typing_ctx_entry list) : t =
    { ctx with t_idents = ents @ ctx.t_idents }

  let extend_tvars ctx (tvs: TA.kind TU.Tvar.t list) : t =
    let ents = List.map (fun e -> CE_tvar e) tvs in
    { ctx with t_idents = ents @ ctx.t_idents }

  let extend_type_ident ctx (p: A.path) (a: int) : t =
    let ent = CE_type_defn_var (p, a) in
    { ctx with t_idents = ent :: ctx.t_idents }

  let extend_nterm_decls ctx (d: A.ident list) : t =
    let ents = List.map (fun e -> CE_non_term_decl e) d in
    { ctx with t_idents = ents @ ctx.t_idents }

  let add_type_defn ctx (td: TA.type_defn) : t =
    let ident = td.TA.type_defn_ident in
    let body  = td.TA.type_defn_body in
    let rep   = body.TA.type_rep in
    let loc   = body.TA.type_rep_loc in
    let ctx =
      match rep with
        | TA.TR_expr _ ->
              (* no variant constructors *)
              ctx
        | TA.TR_variant constrs ->
              (* update global constructors *)
              List.fold_left
                (fun ctx (c, _) ->
                 { ctx with
                   t_var_constrs = StringMap.add (L.value c) loc ctx.t_var_constrs }
                ) ctx constrs
    in { ctx with t_idents = CE_type_defn ([ident], td) :: ctx.t_idents }

  let add_fun_sig ctx (fs: fun_sig) : t =
    let ent = CE_fun_sig ([fs.fun_sig_ident], fs) in
    { ctx with t_idents = ent :: ctx.t_idents }

  let add_nterm_type ctx (ntd: nterm_type) : t =
    (* replace the declaration if present *)
    let rec replace earlier ents =
      match ents with
        | [] ->
              (* if not present, put the definition in the front of
               * the context.
               *)
              CE_non_term_type ntd :: (List.rev earlier)
        | (CE_predefined_type _ as e) :: rest ->
              replace (e :: earlier) rest
        | (CE_tvar _ as e) :: rest ->
              replace (e :: earlier) rest
        | (CE_pvar _ as e) :: rest ->
              replace (e :: earlier) rest
        | (CE_type_defn _ as e) :: rest ->
              replace (e :: earlier) rest
        | (CE_fun_sig _ as e) :: rest ->
              replace (e :: earlier) rest
        | (CE_non_term_decl nt as e) :: rest ->
              if AU.path_equals [nt] ntd.nterm_name
              then (List.rev earlier) @ (CE_non_term_type ntd :: rest)
              else replace (e :: earlier) rest
        | (CE_non_term_type d as e) :: rest ->
              assert (AU.path_equals d.nterm_name ntd.nterm_name = false);
              replace (e :: earlier) rest
        | (CE_type_defn_var _ as e) :: rest ->
              replace (e :: earlier) rest in
    let t_idents = replace [] ctx.t_idents in
    { ctx with t_idents }

  (* checks the arity for the use of a type constructor *)
  let lookup_type_arity ctx (path: A.path) : int option =
    let rec scan ents =
      match ents with
        | [] ->
              None
        | CE_predefined_type (p, a) :: rest ->
              if AU.path_equals p path
              then Some a
              else scan rest
        | CE_type_defn (p, td) :: rest ->
              if AU.path_equals p path
              then Some (List.length td.TA.type_defn_tvars)
              else scan rest
        | CE_type_defn_var (p, a) :: rest ->
              if AU.path_equals p path
              then Some a
              else scan rest
        | _ :: rest ->
              scan rest
    in scan ctx.t_idents

  (* checks if a type name is predefined *)
  let is_predefined ctx (path: A.path) : bool =
    let rec scan ents =
      match ents with
        | [] ->
              false
        | CE_predefined_type (p, _) :: rest ->
              if AU.path_equals p path
              then true
              else scan rest
        | _ :: rest ->
              scan rest
    in scan ctx.t_idents

  (* returns a named type definition if defined *)
  let lookup_type_defn ctx (path: A.path) : TA.type_defn option =
    let rec scan ents =
      match ents with
        | [] ->
              None
        | CE_type_defn (p, td) :: rest ->
              if AU.path_equals p path
              then Some td
              else scan rest
        | _ :: rest ->
              scan rest
    in scan ctx.t_idents

  (* returns the type variable with the given name *)
  let lookup_type_var ctx (tv: A.tvar) : TA.kind TU.Tvar.t option =
    let rec scan ents =
      match ents with
        | [] ->
              None
        | CE_tvar tv' :: rest ->
              let tvn = L.value tv in
              let tvn' = L.value (TU.Tvar.name tv') in
              if tvn = tvn' then Some tv' else scan rest
        | _ :: rest ->
              scan rest
    in scan ctx.t_idents

  (* returns the non-term type definition with the given name *)
  let lookup_non_term ctx (p: A.path) : nterm_type =
    let rec scan ents =
      match ents with
        | [] ->
              type_error (Unknown_non_terminal p) (AU.path_loc p)
        | CE_non_term_type nt :: rest ->
              if AU.path_equals nt.nterm_name p
              then nt
              else scan rest
        | _ :: rest ->
              scan rest
    in scan ctx.t_idents

  (* returns whether a non-term has been declared or defined with the given name *)
  let is_declared_non_term ctx (p: A.path) : bool  =
    let rec scan ents =
      match ents with
        | [] ->
              false
        | CE_non_term_type nt :: rest ->
              if AU.path_equals nt.nterm_name p
              then true
              else scan rest
        | CE_non_term_decl n :: rest ->
              if AU.path_equals [n] p
              then true
              else scan rest
        | _ :: rest ->
              scan rest
    in scan ctx.t_idents

end

(* resolves the path argument starting from a given non-terminal *)
let resolve_path ctx (ntd: nterm_type) (p: A.path) : TA.type_expr =
  (* p is a path to an attribute *)
  let get_attr_type ntd attr =
    match (match AU.param_lookup attr ntd.nterm_inh_attrs with
             | Some d ->  Some d
             | None   ->  AU.param_lookup attr ntd.nterm_syn_attrs
          ) with
      | None ->
            type_error (Undefined_attribute (attr, ntd.nterm_name))
                       (L.loc attr)
      | Some d ->
            d in
  let rec resolve ntd p =
    match p with
      | []  -> (* we should always have non-empty paths *)
            assert false
      | [a] ->
            get_attr_type ntd a
      | a :: path ->
            (match (get_attr_type ntd a).TA.type_expr with
               | TA.TE_non_term ntp ->
                     resolve (Ctx.lookup_non_term ctx ntp) path
               | _ ->
                     type_error (Invalid_path_attribute (a, ntd.nterm_name))
                                (L.loc a)
            )
  in resolve ntd p

(* convert tvar names into tvars, checking uniqueness *)
let mk_typed_tvars (tvs: A.tvar list) : (TA.kind TU.Tvar.t) list =
  let folder (loc_map, tvs) tv =
    let id = L.value tv in
    let idloc = L.loc tv in
    match StringMap.find_opt id loc_map with
      | Some loc ->
            type_error (Nonunique_type_var (tv, loc)) idloc
      | None ->
            let tv = TU.Tvar.mk_tvar TA.K_type tv in
            let loc_map = StringMap.add id idloc loc_map in
            loc_map, (tv :: tvs) in
  let _, tvs =
    List.fold_left folder (StringMap.empty, []) tvs in
  List.rev tvs

(* well-typed check for type expressions; returns the typed-ast
 * version (if valid).
 *)
let rec well_typed_type_expr ctx (te: A.type_expr) : TA.type_expr =
  let loc = te.A.type_expr_loc in
  let mk_te type_expr =
    TA.({ type_expr; type_expr_loc = loc }) in
  match te.A.type_expr with
    | A.TE_tvar tv ->
          (* a valid tvar must occur in the context *)
          (match Ctx.lookup_type_var ctx tv with
             | None ->
                   type_error (Unknown_type_variable tv) (L.loc tv)
             | Some tv' -> mk_te (TA.TE_tvar tv'))
    | A.TE_tuple tl ->
          let tl' = List.map (fun e -> well_typed_type_expr ctx e) tl
          in mk_te (TA.TE_tuple tl')
    | A.TE_list l ->
          mk_te (TA.TE_list (well_typed_type_expr ctx l))
    | A.TE_constr (p, tl) ->
          (match Ctx.lookup_type_arity ctx p with
             | None ->
                   let e = Unknown_type_constructor p in
                   type_error e loc
             | Some expected ->
                   let found = List.length tl in
                   let e = Incorrect_tycon_arity (p, expected, found) in
                   if found <> expected
                   then type_error e loc
          );
          let tl' = List.map (fun e -> well_typed_type_expr ctx e) tl in
          mk_te (TA.TE_constr (p, tl'))
    | A.TE_typeof p ->
          (match p with
             | []  ->  (* we should always have non-empty paths *)
                   assert false
             | [a] ->
                   (* A single element path to typeof() must resolve to a non-terminal. *)
                   if Ctx.is_declared_non_term ctx [a]
                   then TA.({ type_expr     = TE_non_term [a];
                              type_expr_loc = L.loc a })
                   else type_error (Unknown_non_terminal [a]) (L.loc a)
             | a :: path ->
                   let ntd = Ctx.lookup_non_term ctx [a] in
                   resolve_path ctx ntd path)

(* well-typed check for type definitions; returns the typed-ast
 * version of the definition (if valid)
 *)
let well_typed_type_defn ctx (td: A.type_defn) : TA.type_defn =
  let tdi = td.A.type_defn_ident in
  let mk_td tvs tdb =
    TA.({ type_defn_ident = tdi;
          type_defn_tvars = tvs;
          type_defn_body  = tdb;
          type_defn_loc   = td.A.type_defn_loc }) in
  (* ensure this is a new type-defn, and doesn't conflict with a
   * predefined type
   *)
  if Ctx.is_predefined ctx [tdi]
  then type_error (Predefined_type [tdi]) (L.loc tdi);
  (match Ctx.lookup_type_defn ctx [tdi] with
     | Some td -> let loc = td.TA.type_defn_loc in
                  let err = Nonunique_type_defn ([tdi], loc) in
                  type_error err (L.loc tdi)
     | None -> ());
  (* construct new unique tvars for the universal tvars and
   * add them to the context to check the body
   *)
  let tvars = td.A.type_defn_tvars in
  let tvs = mk_typed_tvars tvars in
  let ctx' = Ctx.extend_tvars ctx tvs in
  (* for possibly self-recursive types, add the type ident to the
   * context with its arity
   *)
  let ctx' = Ctx.extend_type_ident ctx' [tdi] (List.length tvars) in
  (* check the definition body with the extended context *)
  let body = td.A.type_defn_body in
  let mk_tr r =
    TA.({ type_rep     = r;
          type_rep_loc = body.A.type_rep_loc }) in
  let chked_rep =
    match body.A.type_rep with
      | A.TR_expr te ->
            TA.TR_expr (well_typed_type_expr ctx' te)
      | A.TR_variant constrs ->
            (* per-constructor handling *)
            let folder (locals, constrs') (c, args) =
              let cid = L.value c in
              let cloc = L.loc c in
              (* Check that the constructors are unique.  For now,
               * check that they are globally unique.
               *)
              (* Check the global constructor map *)
              (match StringMap.find_opt cid ctx'.Ctx.t_var_constrs with
                 | None -> ()
                 | Some loc -> let err = Nonunique_variant_constr (c, loc) in
                               type_error err cloc);
              (* Check and update the local constructor map *)
              let locals =
                match StringMap.find_opt cid locals with
                  | Some loc -> let err = Nonunique_variant_constr (c, loc) in
                                type_error err cloc
                  | None -> StringMap.add cid cloc locals in
              (* Ensure the arguments are well-typed *)
              let args' = List.map (well_typed_type_expr ctx') args in
              locals, ((c, args') :: constrs')
            in
            (* well-typed check for all the constructors *)
            let _, constrs' = List.fold_left folder (StringMap.empty, []) constrs in
            TA.TR_variant constrs'
  (* return the typed-ast version *)
  in mk_td tvs (mk_tr chked_rep)

(* extract the type variables in a type expression *)
let tvars_of_type_expr (te: A.type_expr) : A.tvar StringMap.t =
  let rec traverse acc te =
    match te.A.type_expr with
      | A.TE_tvar tv ->
            (* keep the first occurrence *)
            (let n = L.value tv in
             match StringMap.find_opt n acc with
               | None   -> StringMap.add n tv acc
               | Some _ -> acc)
      | A.TE_tuple tel ->
            List.fold_left (fun ctx e -> traverse ctx e) acc tel
      | A.TE_list te ->
            traverse acc te
      | A.TE_constr (p, tel) ->
            List.fold_left (fun ctx e -> traverse ctx e) acc tel
      | A.TE_typeof p ->
            (* non-terminals are not (yet?) polymorphic *)
            acc
  in traverse StringMap.empty te


(* well-typed check for type signatures of function definitions;
 * returns the function signature (if valid)
 *)
let type_check_fun_sig ctx (fd: A.fun_defn) : fun_sig =
  (* we need to hoist out the (implicitly) universal tvars from the
   * types in the param decls; i.e. we need to convert something like
   *                cons(l: list<'a>, e: 'a) -> list<'a>
   * into
   *   forall ('a), cons(l: list<'a>, e: 'a) -> list<'a>
   *)
  let folder (pmap, tvs, ctx, args) param_decl =
    let pdloc  = L.loc param_decl in
    let pi, pt = L.value param_decl in
    let pname  = L.value pi in
    let ploc   = L.loc pi in
    let pmap   =
      (match StringMap.find_opt pname pmap with
         | Some l -> type_error (Nonunique_fun_param (pi, l)) ploc
         | None   -> StringMap.add pname ploc pmap) in
    let tvs'  = tvars_of_type_expr pt in
    (* add any new type variables to the context *)
    let ctx, tvs =
      StringMap.fold
        (fun n tv (ctx, tvs) ->
         match StringMap.find_opt n tvs with
           | None ->
                 (* Add a new tvar to tvs and the context. *)
                 let tv = TU.Tvar.mk_tvar TA.K_type tv in
                 (Ctx.extend_tvars ctx [tv], StringMap.add n tv tvs)
           | Some _ ->
                 ctx, tvs
        ) tvs' (ctx, tvs) in
    (* now check that pt is well-typed in the updated context *)
    let pt' = well_typed_type_expr ctx pt in
    (pmap, tvs, ctx, (L.mk_loc_val (pi, pt') pdloc) :: args) in
  let _, tvs, ctx, typed_params =
    List.fold_left folder (StringMap.empty, StringMap.empty, ctx, []) fd.A.fun_defn_params in
  (* ensure that the return type is well-typed *)
  let res_type = well_typed_type_expr ctx fd.A.fun_defn_res_type in
  { fun_sig_ident    = fd.A.fun_defn_ident;
    fun_sig_tvars    = List.map (fun (k, v) -> v) (StringMap.bindings tvs);
    fun_sig_params   = List.rev typed_params;
    fun_sig_res_type = res_type;
    fun_sig_loc      = fd.A.fun_defn_loc }


(* well-typed check for types of non-terminal definitions;
 * returns the non-terminal type (if valid).
 *
 * This requires that all typeof dependencies of the non-terminal
 * have had their type definitions added to the context.
 *)
let type_check_nterm_type ctx (nt: A.non_term_defn) : nterm_type =
  let tc_attr pd =
    let aid, ate = L.value pd in
    let ate = well_typed_type_expr ctx ate in
    L.mk_loc_val (aid, ate) (L.loc pd) in
  let nterm_inh_attrs = List.map tc_attr nt.A.non_term_inh_attrs in
  let nterm_syn_attrs = List.map tc_attr nt.A.non_term_syn_attrs in
  { nterm_name = [nt.A.non_term_name];
    nterm_inh_attrs;
    nterm_syn_attrs;
    nterm_loc = nt.A.non_term_loc }


(* Construction of the typeof dependency graph for non-terminal types. *)

module Ordered_Typeof_dep = struct
  type t = typeof_dep
  let compare a b =
    match a, b with
      | Tydep_nterm a, Tydep_nterm b ->
            AU.path_compare a b
      | Tydep_nterm a, Tydep_nterm_attr (b, ba) ->
            AU.path_compare a (b @ [ba])
      | Tydep_nterm_attr (a, aa), Tydep_nterm b ->
            AU.path_compare (a @ [aa]) b
      | Tydep_nterm_attr (a, aa), Tydep_nterm_attr (b, ba) ->
            AU.path_compare (a @ [aa]) (b @ [ba])
end

module TD_depgraph = Depgraph.Make(Ordered_Typeof_dep)

(* compute the typeof() dependencies of a type expression. *)
let typeof_deps_type_expr (te : A.type_expr) : typeof_dep list =
  let rec helper acc te =
    match te.A.type_expr with
      | A.TE_tvar _ -> acc
      | A.TE_tuple tel -> List.fold_left helper acc tel
      | A.TE_list te -> helper acc te
      | A.TE_constr (p, tel) -> List.fold_left helper acc tel
      | A.TE_typeof p ->
            let nt, attr = AU.path_into_nterm_attr p in
            (match attr with
               | None ->
                     Tydep_nterm nt :: acc
               | Some a ->
                     Tydep_nterm nt :: Tydep_nterm_attr (nt, a) :: acc
            )
  in helper [] te

(* compute the typeof() dependencies of a non-terminal.
 * There is an implicit typeof dependency between the type of a non-terminal
 * and the types of its attributes.
 *)
let typeof_deps_non_term (dg : TD_depgraph.t) (nt : A.non_term_defn) : TD_depgraph.t =
  let ntpath = [nt.A.non_term_name] in
  let ntnode = Tydep_nterm ntpath in
  let add_dep dg node dep =
    TD_depgraph.add_link dg node dep in
  let process_attr dg attr =
    let aname, atype = L.value attr in
    let anode = Tydep_nterm_attr (ntpath, aname) in
    let dg = add_dep dg ntnode anode in
    List.fold_left (fun dg dep -> add_dep dg anode dep)
                   dg (typeof_deps_type_expr atype) in
  let dg = List.fold_left process_attr dg nt.A.non_term_inh_attrs in
  List.fold_left process_attr dg nt.A.non_term_syn_attrs

(*

  The tentative type-checking strategy is to use a bi-directional
  typing algorithm, with the following passes:

  - The first pass ensures that all type expressions
    (type-definitions, function type signatures) are well-formed.

    This populates the context with the types of function symbols, and
    the definitions of all predefined and user-defined types.

    During this pass, we construct the $typeof() dependency graph for
    each non-terminal definition.

  - The second pass ensures that the types of each non-terminal node
    are well-formed.  This is done in dependency order, using a
    topological sort of the dependency graph.

  - The next pass then checks the function bodies against this
    context, using the checking mode of the bidirectional algorithm.

  - Each non-terminal definition in the formats are then checked.  The
    exact algorithm here needs to be developed.  It would need to:

    . all constraint expressions have the boolean type

    . perform the usual attribute usage and dependency checks

    . ensure that all attributes are fully initialized before any use,
      and all synthesized attributes are assigned a value at the end
      of the RHS.

 *)

let type_check toplevel =
  (* update context with type and function signatures, while
   * collecting non-terminal type definitions and constructing their
   * dependency graph.
   *)
  let ctx, dgraph, ntdefs =
    List.fold_left
      (fun (ctx, dgraph, ntdefs) d ->
       match d with
         | A.Decl_use _ ->
               (* TODO *)
               ctx, dgraph, ntdefs
         | A.Decl_type td ->
               let td' = well_typed_type_defn ctx td in
               (Ctx.add_type_defn ctx td'), dgraph, ntdefs
         | A.Decl_fun fd ->
               let fs = type_check_fun_sig ctx fd in
               (Ctx.add_fun_sig ctx fs), dgraph, ntdefs
         | A.Decl_nterm d ->
               (Ctx.extend_nterm_decls ctx d.A.nterms), dgraph, ntdefs
         | A.Decl_format f ->
               (* update the dependency graph *)
               let dgraph, ntdefs =
                 List.fold_left
                   (fun (dg, df) fd ->
                    match fd.A.format_decl with
                      | A.Format_decl_non_term d ->
                            (* TODO: use paths for non-terminal names
                             * with format name prefixes *)
                            let p = [d.A.non_term_name] in
                            let nm = AU.str_of_path p in
                            let dg = typeof_deps_non_term dg d in
                            let df = StringMap.add nm d df in
                            dg, df
                   ) (dgraph, ntdefs) f.A.format_decls in
               (* note: we could eagerly check for cyclic dependencies
                * here for better error location information, at the
                * expense of redundant checking.
                *)
               ctx, dgraph, ntdefs
      )
      (Ctx.init (), TD_depgraph.init, StringMap.empty)
      toplevel.A.decls in
  (* sort the non-terminal dependencies *)
  let sorted =
    try TD_depgraph.topo_sort dgraph
    with
      | TD_depgraph.Node_not_present d ->
            type_error (Undefined_path (path_of_dep d)) (loc_of_dep d)
      | TD_depgraph.Cycle c ->
            (* this is a global error, but we need to ascribe a
             * location to it.  for now, use the location of the first
             * dependency in the cycle.
             *)
            let loc = loc_of_dep (List.hd c) in
            type_error (Cyclic_typeof_dependency c) loc in
  (* perform the well-formed check for non-terminal types in order *)
  let ctx =
    List.fold_left
      (fun ctx dep ->
       match dep with
         | Tydep_nterm p ->
               let nm = AU.str_of_path p in
               let ntd =
                 (match StringMap.find_opt nm ntdefs with
                    | Some df ->
                          df
                    | None ->
                          let err = Undefined_path p in
                          let loc = loc_of_dep dep in
                          type_error err loc) in
               let ntt = type_check_nterm_type ctx ntd in
               Ctx.add_nterm_type ctx ntt
         | Tydep_nterm_attr _ ->
               (* these should always have the corresponding nterm
                * node which are processed above
                *)
               ctx
      ) ctx (List.rev sorted)
  in ignore ctx
