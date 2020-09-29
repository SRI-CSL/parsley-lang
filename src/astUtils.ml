open Ast

let to_tname (id : ident) =
  MultiEquation.TName (Location.value id)

(* constructing type expressions *)

let make_tvar_ident (id : ident) : type_expr =
  { type_expr = TE_tvar id;
    type_expr_loc = Location.loc id }

let make_tvar_name (name : string) loc : type_expr =
  { type_expr = TE_tvar (Location.mk_loc_val name loc);
    type_expr_loc = loc }

let make_type_app_name (name : string) (args : type_expr list) loc
    : type_expr =
  let c = make_tvar_name name loc in
  { type_expr = TE_tapp (c, args);
    type_expr_loc = loc }

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
      | TE_tapp ({type_expr = TE_tvar c}, h :: res :: [])
           when Location.value c = "->" ->
          helper (h :: acc) res
      | _ -> typ :: acc in
  helper [] typ

let add_arrow_result (typ : type_expr) (res : type_expr) : type_expr =
  (* adds a result type to an arrow type *)
  let args = arrow_args typ in
  make_arrow_type (args @ [res]) typ.type_expr_loc

(* constructing pattern expressions and expressions *)

let make_pattern_loc (pat : pattern_desc) loc =
  { pattern = pat;
    pattern_loc = loc }

let make_expr_loc (exp : expr_desc) loc =
  { expr = exp;
    expr_loc = loc }

(* sorting record fields into canonical order *)
let sort_fields fields =
  List.sort (fun (f1,_) (f2,_) ->
      String.compare (Location.value f1) (Location.value f2)
    ) fields
