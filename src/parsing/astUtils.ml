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

open Ast

let to_tname (id : ident) =
  TName (Location.value id)

(* constructing type expressions *)

let make_tvar_ident (id : ident) : type_expr =
  {type_expr = TE_tvar id;
   type_expr_loc = Location.loc id}

let make_tvar_name (name : string) loc : type_expr =
  {type_expr = TE_tvar (Location.mk_loc_val name loc);
   type_expr_loc = loc}

let make_type_app_name (name : string) (args : type_expr list) loc
    : type_expr =
  let c = make_tvar_name name loc in
  {type_expr = TE_tapp (c, args);
   type_expr_loc = loc}

let rec make_arrow_type (args : type_expr list) loc : type_expr =
  match args with
    | [] -> assert false
    | [r] -> r  (* no arrow *)
    | h :: t ->
        let res = make_arrow_type t loc in
        make_type_app_name "->" [h; res] loc

let arrow_args (typ : type_expr) : type_expr list =
  let rec helper acc typ =
    match typ.type_expr with
      | TE_tapp ({type_expr = TE_tvar c; _}, h :: res :: [])
           when Location.value c = "->" ->
          helper (h :: acc) res
      | _ -> typ :: acc in
  List.rev (helper [] typ)

let add_arrow_result (typ : type_expr) (res : type_expr) : type_expr =
  (* adds a result type to an arrow type *)
  let args = arrow_args typ in
  make_arrow_type (args @ [res]) typ.type_expr_loc

(* constructing pattern expressions and expressions *)

let make_pattern_loc (type b) (pat : (unit, b) pattern_desc) loc =
  {pattern = pat;
   pattern_loc = loc;
   pattern_aux = ()}

let make_expr_loc (type b) (exp : (unit, b) expr_desc) loc =
  {expr = exp;
   expr_loc = loc;
   expr_aux = ()}

(* sorting record fields into canonical order *)
let sort_fields fields =
  List.sort (fun (f1,_) (f2,_) ->
      String.compare (Location.value f1) (Location.value f2)
    ) fields

(* utilities to make ast types comparable by syntactical equality, by
   normalizing location and aux information *)

let unwrap_id id =
  Location.mk_loc_val (Location.value id) Location.ghost_loc

let unwrap_var v =
  Location.mk_loc_val (var_name v, ()) Location.ghost_loc

let unwrap_constructor (typ, constr) =
  (Location.value typ, Location.value constr)

let rec unwrap_typ typ =
  let t = match typ.type_expr with
      | TE_tvar t ->
          TE_tvar (unwrap_id t)
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
          P_variant (c, List.map unwrap_pat ps) in
  {pattern = p; pattern_loc = Location.ghost_loc; pattern_aux = ()}

let rec unwrap_exp exp =
  let e = match exp.expr with
      | E_var v ->
          E_var (unwrap_var v)
      | E_constr ((t, c), es) ->
          let t, c = unwrap_id t, unwrap_id c in
          E_constr ((t, c), List.map unwrap_exp es)
      | E_record fs ->
          E_record (List.map
                      (fun (f, e) ->
                        (unwrap_id f, unwrap_exp e)
                      ) fs)
      | E_apply (f, es) ->
          E_apply (unwrap_exp f, List.map unwrap_exp es)
      | E_unop (op, e) ->
          E_unop (op, unwrap_exp e)
      | E_binop (op, l, r) ->
          E_binop (op, unwrap_exp l, unwrap_exp r)
      | E_match (e, (t, c)) ->
          E_match (unwrap_exp e, (unwrap_id t, unwrap_id c))
      | E_literal l ->
          E_literal l
      | E_field (e, f) ->
          E_field (unwrap_exp e, unwrap_id f)
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

(** [canonicalize_dcon typ constr] returns the canonical name for the
    data constructor [constr] of type [typ]. *)
let canonicalize_dcon typ constr =
  Printf.sprintf "%s::%s" typ constr
