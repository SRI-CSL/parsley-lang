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

type raw_type_expr  = raw_mod gen_type_expr

(* convert a filename to a module name *)
let modname_of_file f : string =
  let m = Filename.basename f in
  let m = Filename.remove_extension m in
  String.capitalize_ascii m

(* module qualifier utils *)

(* a comparator compatible with `OrderedType.compare`. *)
let mod_compare m m' =
  match m, m' with
    | Modul (Mod_explicit m), Modul (Mod_explicit m') ->
        compare (Location.value m) (Location.value m')
    | Modul (Mod_inferred m), Modul (Mod_inferred m') ->
        compare m m'
    | Modul (Mod_explicit m), Modul (Mod_inferred m') ->
        compare (Location.value m) m'
    | Modul (Mod_inferred m), Modul (Mod_explicit m') ->
        compare m (Location.value m')
    | _ ->
        compare m m'

let mod_equiv m m' =
  0 = mod_compare m m'

let qual_compare (m, t) (m', t') =
  let mc = mod_compare m m' in
  if mc = 0 then compare t t' else mc

let stdlib: mod_qual modul =
  Modul Mod_stdlib

let infer_mod (m: string) : mod_qual modul =
  Modul (Mod_inferred m)

(* manipulating names and identifiers *)

let mk_modprefix (m: mname) =
  match m with
    | Modul (Mod_explicit m) -> (Location.value m) ^ "."
    | Modul (Mod_inferred m) -> m ^ "."
    | Modul Mod_stdlib       -> ""

let str_of_mod (m: mname) =
  match m with
    | Modul (Mod_explicit m) -> (Location.value m)
    | Modul (Mod_inferred m) -> Printf.sprintf "(%s)" m
    | Modul Mod_stdlib       -> ""

(** [canonicalize_dcon typ constr] returns the canonical name for the
    data constructor [constr] of type [typ]. *)
let canonicalize_dcon typ constr =
  Printf.sprintf "%s::%s" typ constr

(** [is_valid_nonterm_name n] checks whether [n] is valid as the
    name of a non-terminal, i.e. it is capitalized *)
let is_valid_nonterm_name n =
  (String.length n > 0) && Char.uppercase_ascii n.[0] = n.[0]

(* printing utilities *)

let str_of_full_tname (m, TName t) =
  (str_of_mod m) ^ "." ^ t

let str_of_full_dname (m, DName d) =
  (str_of_mod m) ^ "." ^ d

let str_of_full_lname (m, LName l) =
  (str_of_mod m) ^ "." ^ l

let str_of_full_nname (m, NName n) =
  (str_of_mod m) ^ "." ^ n

let str_of_full_vname (m, VName v) =
  (str_of_mod m) ^ "." ^ v

(* constructing type expressions *)

let make_tvar (type m) (id: ident) : m gen_type_expr =
  {type_expr     = TE_tvar id;
   type_expr_loc = Location.loc id}

let make_tname (name: string) loc : raw_type_expr =
  {type_expr     = TE_tname (Modul None, Location.mk_loc_val name loc);
   type_expr_loc = loc}

let make_std_tname (name: string) loc : type_expr =
  {type_expr     = TE_tname (Modul Mod_stdlib, Location.mk_loc_val name loc);
   type_expr_loc = loc}

let make_mod_tname (m: mname) (name: string) loc : type_expr =
  {type_expr     = TE_tname (m, Location.mk_loc_val name loc);
   type_expr_loc = loc}

let make_raw_tname_id (id: ident) : raw_type_expr =
  let loc = Location.loc id in
  {type_expr     = TE_tname (Modul None, id);
   type_expr_loc = loc}

let make_raw_mod_tname_id (m: modident) (id: ident) : raw_type_expr =
  let loc = Location.extent (Location.loc m) (Location.loc id) in
  {type_expr     = TE_tname (Modul (Some m), id);
   type_expr_loc = loc}

let make_tname_id (m: mname) (id: ident) : type_expr =
  let loc = Location.loc id in
  {type_expr     = TE_tname (m, id);
   type_expr_loc = loc}

let make_raw_type_app (name: string) (args: raw_type_expr list) loc
    : raw_type_expr =
  let c = make_tname name loc in
  {type_expr     = TE_tapp (c, args);
   type_expr_loc = loc}

let make_raw_type_app_id (id: ident) (args: raw_type_expr list) loc
    : raw_type_expr =
  let c = make_raw_tname_id id in
  {type_expr     = TE_tapp (c, args);
   type_expr_loc = loc}

let make_raw_type_app_mod_id (m: modident) (id: ident) (args: raw_type_expr list) loc
    : raw_type_expr =
  let c = make_raw_mod_tname_id m id in
  {type_expr     = TE_tapp (c, args);
   type_expr_loc = loc}

let rec make_raw_arrow_type (args: raw_type_expr list) loc : raw_type_expr =
  match args with
    | []     -> assert false
    | [r]    -> r  (* no arrow *)
    | h :: t -> let res = make_raw_arrow_type t loc in
                make_raw_type_app "->" [h; res] loc

let make_std_type_app (name: string) (args: type_expr list) loc
    : type_expr =
  let c = make_std_tname name loc in
  {type_expr     = TE_tapp (c, args);
   type_expr_loc = loc}

let make_mod_type_app (m: mname) (name: string) (args: type_expr list) loc
    : type_expr =
  let c = make_mod_tname m name loc in
  {type_expr     = TE_tapp (c, args);
   type_expr_loc = loc}

let rec make_arrow_type (args: type_expr list) loc : type_expr =
  match args with
    | []     -> assert false
    | [r]    -> r  (* no arrow *)
    | h :: t -> let res = make_arrow_type t loc in
                make_std_type_app "->" [h; res] loc

let arrow_args (typ: type_expr) : type_expr list =
  let rec helper acc typ =
    match typ.type_expr with
      | TE_tapp ({type_expr = TE_tname (Modul Mod_stdlib, c); _}, h :: res :: [])
           when Location.value c = "->" ->
          helper (h :: acc) res
      | _ -> typ :: acc in
  List.rev (helper [] typ)

let add_arrow_result (typ: type_expr) (res: type_expr)
    : type_expr =
  (* adds a result type to an arrow type *)
  let args = arrow_args typ in
  make_arrow_type (args @ [res]) typ.type_expr_loc

let make_bitvector_type (n: int) loc : type_expr =
  assert (n > 0);
  let n = make_std_tname (string_of_int n) loc in
  make_std_type_app "bitvector" [n] loc

(* constructing expression variables *)

let make_var v =
  let s = Location.value v in
  let l = Location.loc v in
  Location.mk_loc_val (s, ()) l

(* constructing pattern expressions and expressions *)

let make_pattern_loc (type b m) (pat: (unit, b, m) pattern_desc) loc =
  {pattern     = pat;
   pattern_loc = loc;
   pattern_aux = ()}

let make_expr_loc (type b m) (exp: (unit, b, m) expr_desc) loc =
  {expr     = exp;
   expr_loc = loc;
   expr_aux = ()}

(* sorting record fields into canonical order *)
let sort_fields fields =
  List.sort (fun ((m1, f1), _) ((m2, f2), _) ->
      let f, f' = (m1, Location.value f1), (m2, Location.value f2) in
      qual_compare f f'
    ) fields

(* integer literal checks *)

let check_int_literal ((s, w): num_t) (i: int) =
  match s, w with
    | S_unsigned, NW_8  ->
        0 <= i && i < 256
    | S_unsigned, NW_16 ->
        0 <= i && i < 65536
    | S_unsigned, NW_32 ->
        0 <= i && i < 4294967296
    | S_unsigned, NW_64
    | S_unsigned, NW_size ->
        0 <= i
    | S_signed, NW_8  ->
        -128 <= i && i < 128
    | S_signed, NW_16 ->
        -32768 <= i && i < 32768
    | S_signed, NW_32 ->
        -2147483648 <= i && i < 2147483648
    | S_signed, NW_64
    | S_signed, NW_size ->
        true
