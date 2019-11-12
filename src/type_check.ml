module A  = Ast
module AU = Ast_utils
module TA = Typed_ast
module TU = Typing_utils
module L  = Location

module StringMap = AU.StringMap

type type_error =
  | Nonunique_type_var of A.tvar * L.t
  | Nonunique_type_defn of A.path * L.t
  | Nonunique_variant_constr of A.ident * L.t
  | Nonunique_fun_param of A.ident * L.t
  | Unknown_type_variable of A.tvar
  | Unknown_type_constructor of A.path
  | Predefined_type of A.path
  | Incorrect_tycon_arity of A.path * (* expected *) int * (* found *) int

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
  | Predefined_type p ->
        Printf.sprintf "cannot re-define predefined type %s"
                       (Ast_utils.str_of_path p)
  | Incorrect_tycon_arity (p, exp, fnd) ->
        Printf.sprintf "%d args expected for %s, found %d"
                       exp (Ast_utils.str_of_path p) fnd

let type_error e loc =
  raise (Error (e, loc))

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
    (* user function definition *)
    | CE_fun_defn of A.path * TA.fun_defn
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
    let mk_predefined id =
      L.mk_loc_val id (L.make_ghost_loc ()) in
    { (* populate with predefined base types *)
      t_idents = [
        CE_predefined_type ([mk_predefined "int"], 0)
      ];
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
end

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
          (* TODO.
           * Note: p might resolve to a non-term, or an attribute of
           * a non-term.  In the latter case, we should use the type
           * of the attribute.
           *)
          Printf.fprintf stderr
              "Warning: type-check of $typeof (for %s) is not yet implemented.\n"
              (AU.str_of_path p);
          mk_te (TA.TE_non_term p)

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

let type_check_fun_def ctx fd =
  (* we need to hoist out the (implicitly) universal tvars from the
   * types in the param decls; i.e. we need to convert something like
   *                cons(l: list<'a>, e: 'a) -> list<'a>
   * into
   *   forall ('a), cons(l: list<'a>, e: 'a) -> list<'a>
   *)
  let folder (pmap, tvs, ctx, args) param_decl =
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
    (pmap, tvs, ctx, (pi, pt') :: args) in
  let _, tvs, ctx, typed_params =
    List.fold_left folder (StringMap.empty, StringMap.empty, ctx, []) fd.A.fun_defn_params in
  (* ensure that the return type is well-typed *)
  let res_type = well_typed_type_expr ctx fd.A.fun_defn_res_type in
  (* TODO: type-check the body *)
  res_type

let type_check toplevel =
  ignore (List.fold_left
    (fun ctx d ->
     match d with
       | A.Decl_use _ ->
             (* TODO *)
             ctx
       | A.Decl_type td ->
             let td' = well_typed_type_defn ctx td in
             Ctx.add_type_defn ctx td'
       | A.Decl_fun fd ->
             let _ = type_check_fun_def ctx fd in
             ctx
       | A.Decl_format _ ->
             (* TODO *)
             ctx
    ) (Ctx.init ()) toplevel.A.decls)
