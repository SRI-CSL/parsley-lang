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

(** This module implements a typing environment useful for type inference. *)

open Parsing
open TypeAlgebra
open Ast
open TypingExceptions

module StringMap = Misc.StringMap

(** {2 Typing environment} *)

(** [type_info] denotes information collected during the user-defined
    type constructor analysis. *)

type bitfield_info =
  {bf_name:   string;
   bf_fields: (string * (int * int)) list;
   bf_length: int}

type record_info =
  {adt:                ident;
   modul:              Ast.mname;
   fields:             (ident * type_expr) list;
   record_constructor: Ast.tname * MultiEquation.variable; (* named "<adt>" *)
   field_destructors:  (lname * MultiEquation.variable) list;
   bitfield_info:      bitfield_info option}

(* The following information is stored for each type constructor:
   - its kind ;
   - its associated term (a type variable actually) ;
   - if it is a variant datatype, the list of its datatype constructors;
     or if it is a record datatype, the list of its record field
     destructors. *)
type algebraic_datatype =
  | Variant of (dname * MultiEquation.variable) list
  | Record of record_info

type adt_info =
  {adt: algebraic_datatype;
   loc: Location.t}

type type_info =
  KindInferencer.t * MultiEquation.variable * adt_info option ref

type type_abbrev = {type_abbrev_tvars: Ast.tname list;
                    type_abbrev_type:  Ast.type_expr}

(* The following information is stored for each datatype constructor:
   - its arity ;
   - its type variables ;
   - its type *)
type data_constructor = int * MultiEquation.variable list * MultiEquation.crterm

(* The following information is stored for each record constructor:
   - its type variables ;
   - its type *)
type record_constructor = MultiEquation.variable list * MultiEquation.crterm

(* The following information is stored for each field destructor:
   - its type variables ;
   - its type *)
type field_destructor = MultiEquation.variable list * MultiEquation.crterm

(** A non-terminal's type definition *)
type non_term_inh_type =
  (MultiEquation.crterm * Location.t) StringMap.t
  * (int Ast.var * Ast.type_expr * MultiEquation.crterm) list

type non_term_syn_type =
  (* aliased to another type, either declared or inferred *)
  | NTT_type of MultiEquation.crterm * record_info option
  (* a monomorphic record of its synthesized attributes *)
  | NTT_record of MultiEquation.variable * record_info option ref
type non_term_type = non_term_inh_type * non_term_syn_type

(* Module type information indexed by fully-qualified names. *)

(* type names *)
module TNameMap = Map.Make(struct
                      type t = full_tname
                      let compare = AstUtils.qual_compare
                    end)
(* data constructors *)
module DNameMap = Map.Make(struct
                      type t = full_dname
                      let compare = AstUtils.qual_compare
                    end)
(* record fields *)
module LNameMap = Map.Make(struct
                      type t = full_lname
                      let compare = AstUtils.qual_compare
                    end)
(* values (functions and constants) *)
module VNameMap = Map.Make(struct
                      type t = full_vname
                      let compare = AstUtils.qual_compare
                    end)
(* non-terminals *)
module NNameMap = Map.Make(struct
                      type t = full_nname
                      let compare = AstUtils.qual_compare
                    end)

(* type signature of a value, and if it is foreign *)
type val_info =
  {val_type:    MultiEquation.variable list * MultiEquation.crterm;
   val_foreign: bool}

(** [environment] denotes typing information associated to identifiers. *)
type environment =
  {type_abbrev:        (Location.t * type_abbrev) TNameMap.t;
   type_info:          type_info TNameMap.t;
   data_constructor:   data_constructor DNameMap.t;
   record_constructor: record_constructor TNameMap.t;
   field_destructor:   field_destructor LNameMap.t;

   (* map constructors and destructors to their owning ADT *)
   datacon_adts: (full_tname * Location.t) DNameMap.t;
   field_adts:   (full_tname * Location.t) LNameMap.t;

   (* value components *)
   values:       (val_info * Location.t) VNameMap.t;

   (* non-terminal types *)
   non_terms:    (non_term_type * Location.t) NNameMap.t;

   (* current module *)
   cur_module:   string}

let empty_environment =
  {type_abbrev        = TNameMap.empty;
   type_info          = TNameMap.empty;
   data_constructor   = DNameMap.empty;
   record_constructor = TNameMap.empty;
   field_destructor   = LNameMap.empty;

   datacon_adts = DNameMap.empty;
   field_adts   = LNameMap.empty;
   values       = VNameMap.empty;

   non_terms    = NNameMap.empty;

   cur_module   = ""}

let add_type_variable env t (k, v) =
  assert (MultiEquation.((UnionFind.find v).kind) != Constant);
  {env with
    type_info = TNameMap.add t (k, v, ref None) env.type_info}

let add_type_variables var_env env =
  let folder = fun env (x, ((_, v, _) as k)) ->
    assert (MultiEquation.((UnionFind.find v).kind) != Constant);
    TNameMap.add x k env in
  {env with
    type_info = List.fold_left folder env.type_info var_env}

let add_type_abbrev env pos t x =
  match TNameMap.find_opt t env.type_abbrev with
    | None ->
        {env with type_abbrev = TNameMap.add t (pos, x) env.type_abbrev}
    | Some _ ->
        raise (Error (pos, DuplicateTypeDefinition t))

let add_type_constructor env pos t x =
  match TNameMap.find_opt t env.type_info with
    | None ->
        {env with type_info = TNameMap.add t x env.type_info}
    | Some _ ->
        raise (Error (pos, DuplicateTypeDefinition t))

let add_data_constructor env loc ((m,_) as adt) dc x =
  let mdc = m, dc in
  match DNameMap.find_opt mdc env.datacon_adts with
    | None ->
        {env with
          data_constructor = DNameMap.add mdc x env.data_constructor;
          datacon_adts     = DNameMap.add mdc (adt, loc) env.datacon_adts}
    | Some (adt, loc') ->
        raise (Error (loc, DuplicateDataConstructor (mdc, adt, loc')))

let add_record_constructor env adt x =
  {env with record_constructor = TNameMap.add adt x env.record_constructor}

let add_field_destructor env loc ((m,_) as adt) ((m',_) as mfd) f =
  (if   AstUtils.mod_compare m m' != 0
   then raise (Error (loc, InconsistentRecordModule (adt, mfd))));
  match LNameMap.find_opt mfd env.field_adts with
    | None ->
        {env with
          field_destructor = LNameMap.add mfd f env.field_destructor;
          field_adts       = LNameMap.add mfd (adt, loc) env.field_adts}
    | Some (adt, loc') ->
        raise (Error (loc, DuplicateRecordField (mfd, adt, loc')))

let add_value env loc vid val_type val_foreign =
  let v = {val_type; val_foreign} in
  let values =
    match VNameMap.find_opt vid env.values with
      | None        -> VNameMap.add vid (v, loc) env.values
      | Some (_, l) -> raise (Error (loc, DuplicateModItem (vid, l))) in
  {env with values}

let crterm_of_non_term_type = function
  | NTT_type (t, _)   -> t
  | NTT_record (v, _) -> CoreAlgebra.TVariable v

let add_non_terminal env loc nt x =
  match NNameMap.find_opt nt env.non_terms with
    | None ->
        {env with non_terms = NNameMap.add nt (x, loc) env.non_terms}
    | Some (_, ploc) ->
        raise (Error (loc, DuplicateNonTerminal (nt, ploc)))

let lookup_non_term env nt =
  match NNameMap.find_opt nt env.non_terms with
    | None -> None
    | Some ((inh, syn), _) ->
        Some (inh, crterm_of_non_term_type syn, syn)

let lookup_non_term_type env nt =
  match NNameMap.find_opt nt env.non_terms with
    | None -> None
    | Some ((_, syn), _) -> Some (crterm_of_non_term_type syn)

(** [lookup_typcon ?pos env t] retrieves typing information about
    the type constructor [t]. *)
let lookup_typcon ?pos env t =
  match TNameMap.find_opt t env.type_info with
    | Some ((_, v, _) as x)
         when MultiEquation.((UnionFind.find v).kind) = Constant ->
        x
    | _ ->
        raise (Error (Location.loc_or_ghost pos, UnboundTypeIdentifier t))

(** [find_typcon env t] looks for typing information related to
    the type constructor [t] in [env]. *)
let find_typcon env t =
  match TNameMap.find_opt t env.type_info with
    | Some ((_, v, _) as x)
         when MultiEquation.((UnionFind.find v).kind) = Constant ->
        Some x
    | _ ->
        None

(** [lookup_type_variable env v] looks for typing information related to
    the type variable [v] in [env]. *)
let lookup_type_variable ?pos env k =
  match TNameMap.find_opt k env.type_info with
    | Some (_, v, _) ->
        CoreAlgebra.TVariable v
    | None ->
        raise (Error (Location.loc_or_ghost pos, UnboundTypeVariable k))

let lookup_value pos env vid =
  match VNameMap.find_opt vid env.values with
    | None        -> raise (Error (pos, UnknownModItem vid))
    | Some (t, _) -> t.val_type, t.val_foreign

(* The kind inferencer wants a view on the environment that
   concerns only the kinds. *)
let as_kind_env env =
  let env = ref env in
  let read id loc =
    match TNameMap.find_opt id (!env).type_info with
      | Some (k, _, _) ->
          k
      | None ->
          raise (Error (loc, UnboundTypeConstructor id)) in
  let update i k =
    env := add_type_variable (!env) i (k, MultiEquation.(variable Flexible ())) in
  (read : full_tname -> Location.t -> KindInferencer.t),
  (update : full_tname -> KindInferencer.t -> unit)

let fold_type_info f init env =
  TNameMap.fold f env.type_info init

(* Some accessors. *)

let typcon_variable env t =
  CoreAlgebra.TVariable (Misc.proj2_3 (lookup_typcon env t))

let as_fun tenv name =
  match find_typcon tenv name with
    | None           -> lookup_type_variable tenv name
    | Some (_, v, _) -> CoreAlgebra.TVariable v

(** [lookup_adt env t] gives access to the typing information for the
    type with name [t]. *)
let lookup_adt env t =
  match TNameMap.find_opt t env.type_info with
    | Some (_, _, adt_ref) -> !adt_ref
    | None                 -> None

(** [lookup_type_abbreviation env t] returns the type abbreviation for [t]
    if present in the environment *)
let lookup_type_abbrev env t =
  match TNameMap.find_opt t env.type_abbrev with
    | Some (_, te) -> Some te
    | None         -> None

(** [is_{defined,variant,record}_type env t] check whether the type
    with name [t] is defined in [env] and is of the appropriate type. *)
let is_defined_type env t =
  match TNameMap.find_opt t env.type_info with
    | Some _ -> true
    | None   -> false

let is_variant_type env t =
  match lookup_adt env t with
    | Some {adt = Variant _; _} -> true
    | _                         -> false

let is_record_type env t =
  match lookup_adt env t with
    | Some {adt = Record _; _} -> true
    | _                        -> false

let get_record_info env t =
  match lookup_adt env t with
    | Some {adt = Record info; _} -> Some info
    | _                           -> None

(** [lookup_datacon env k] looks for typing information related to
    the fully qualified data constructor [k] in [env]. *)
let lookup_datacon env pos k =
  match DNameMap.find_opt k env.data_constructor with
    | Some x -> x
    | None   -> raise (Error (pos, UnboundDataConstructor k))

(** [lookup_field_destructor env f] looks for typing information
    for the destructor of the record field [f] in [env]. *)
let lookup_field_destructor env pos f =
  match LNameMap.find_opt f env.field_destructor with
    | Some x -> x
    | None   -> raise (Error (pos, UnboundRecordField f))

(** [lookup_record_constructor env adt] looks for typing information
    for the constructor of the record [adt] in [env]. *)
let lookup_record_constructor env pos adt =
  match TNameMap.find_opt adt env.record_constructor with
    | Some x -> x
    | None   -> raise (Error (pos, UnboundRecord adt))

let lookup_datacon_adt env k =
  match DNameMap.find_opt k env.datacon_adts with
    | Some (adt, _) -> Some adt
    | None          -> None

let lookup_field_adt env k =
  match LNameMap.find_opt k env.field_adts with
    | Some (adt, _) -> Some adt
    | None          -> None

let rigid_args rt =
  List.fold_left (fun acu ->
      function
      | CoreAlgebra.TVariable v ->
          if   MultiEquation.((UnionFind.find v).kind = Rigid)
          then v :: acu
          else acu
      | _ -> acu
    ) [] (tycon_args rt)

let fresh_scheme kvars kt =
  let fresh_kvars =
    let mkvar ?name _v = MultiEquation.(variable Flexible ?name ()) in
    List.map mkvar kvars in
  let fresh_kvars_assoc = List.combine kvars fresh_kvars in
  (fresh_kvars, CoreAlgebra.change_arterm_vars fresh_kvars_assoc kt)

let fresh_datacon_scheme tenv loc k =
  let (_, kvars, kt) = lookup_datacon tenv loc k in
  fresh_scheme kvars kt

let fresh_field_destructor_scheme tenv loc f =
  let (kvars, kt) = lookup_field_destructor tenv loc f in
  fresh_scheme kvars kt

let is_regular_datacon_scheme tenv adt_name kvars kt =
  let rt = result_type (as_fun tenv) kt in
  (* Check that all the tycon arguments are distinct rigid variables. *)
  let rigid_args = rigid_args rt in
  let check_args =
    List.for_all (fun v -> List.memq v kvars) rigid_args
    && List.length rigid_args = List.length kvars in
  (* Check that the result type is the adt itself. *)
  let name = match tycon_name rt with
      | TVariable v -> (UnionFind.find v).name
      | _           -> None in
  let check_result = match name with
      | Some n -> n = adt_name
      | None   -> false in
  check_args && check_result

let is_regular_field_scheme tenv adt_name kvars kt =
  let kargs = arg_types (as_fun tenv) kt in
  match kargs with
    | [] -> false  (* a destructor needs an argument *)
    | rt :: _ ->
        (* Check that all the tycon arguments are distinct rigid variables. *)
        let rigid_args = rigid_args rt in
        let check_args =
          List.for_all (fun v -> List.memq v kvars) rigid_args
          && List.length rigid_args = List.length kvars in
        (* Check that the source type is the adt itself. *)
        let name = match tycon_name rt with
            | TVariable v -> (UnionFind.find v).name
            | _           -> None in
        let check_source = match name with
            | Some n -> n = adt_name
            | None   -> false in
        check_args && check_source

let fresh_unnamed_rigid_vars _pos _env vars =
  let rqs, denv = MultiEquation.(variable_list Rigid vars) in
  (rqs,
   List.map (function
       | (n, CoreAlgebra.TVariable v) -> (n, (KindInferencer.fresh_kind (), v, ref None))
       | _                            -> assert false
     ) denv)
