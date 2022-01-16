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

(* the source of the data in a view *)
type source =
  | Src_file of string (* unmodified data from file *)
  | Src_transform      (* transformed by user program *)

(* internal representation of a buffer *)
module ViewBuf = struct
  type t =
    (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

  let size (b: t) : int =
    Bigarray.Array1.size_in_bytes b
end

(* a view is a subrange of a buffer, currently represented by a
   possibly shared fixed-length byte sequence. *)

type view =
  {vu_buf:    ViewBuf.t;
   vu_source: source;
   vu_id:     Int64.t; (* unique identifier per view *)

   (* all locations below are absolute indices into vu_buf.
      The following invariants are maintained:
      . vu_end is 1 past the last valid read index for the buffer
      . 0 <= vu_start <= vu_ofs <= vu_end
      . it is legal for vu_ofs = vu_end; however, it is illegal to use
        that offset for a read.
    *)
   vu_start:  int;
   vu_ofs:    int;     (* cursor, i.e. index for next read *)
   vu_end:    int}

(* the values of the expression language.  sets and maps have an
   inefficient representation since the Set and Map functors in
   OCaml's stdlib give predicative types, and those in `value` are
   impredicative. *)
type bitfield_info = Typing.TypingEnvironment.bitfield_info
type value =
  | V_unit
  | V_bool of bool
  | V_bit of bool
  | V_char of char (* also used for byte *)
  | V_int of Int64.t
  | V_float of float
  | V_string of string
  | V_bitvector of bool list                (* big-endian *)
  | V_bitfield of bitfield_info * bool list (* big-endian *)
  | V_option of value option
  | V_list of value list
  | V_tuple of value list
  | V_constr of (string * string) * value list
  | V_record of (string * value) list
  (* module types *)
  | V_view of view
  | V_set of value list
  | V_map of (value * value) list

(* a type to describe the runtime type of the value *)
type vtype =
  | T_empty (* used for empty options, lists, sets and maps *)
  | T_unit
  | T_bool
  | T_bit
  | T_char
  | T_byte
  | T_int
  | T_float
  | T_string
  | T_bitvector
  | T_option of vtype
  | T_list of vtype
  | T_tuple of vtype list
  | T_adt of string
  | T_adt_constr of (string * string) * vtype list
  | T_record of (string * vtype) list
  | T_view
  | T_set of vtype
  | T_map of vtype * vtype

let rec string_of_vtype (t: vtype) : string =
  let string_of_field (f, ft) =
    Printf.sprintf "%s: %s" f (string_of_vtype ft) in
  match t with
    | T_empty     -> "unknown"  (* should never get here; assert? *)
    | T_unit      -> "unit"
    | T_bool      -> "bool"
    | T_bit       -> "bit"
    | T_char      -> "char"
    | T_byte      -> "byte"
    | T_int       -> "int"
    | T_float     -> "float"
    | T_string    -> "string"
    | T_bitvector -> "bitvector"

    | T_option T_empty -> "option<>"
    | T_option t'      -> Printf.sprintf "option<%s>" (string_of_vtype t')

    | T_list T_empty -> Printf.sprintf "list<>"
    | T_list t'      -> Printf.sprintf "list<%s>" (string_of_vtype t')

    | T_tuple ts    -> "("
                       ^ (String.concat ", " (List.map string_of_vtype ts))
                       ^ ")"
    | T_adt s       -> s
    | T_adt_constr ((t', c), ts) -> Printf.sprintf "%s::%s(%s)" t' c
                                      (String.concat ", " (List.map string_of_vtype ts))
    | T_record fs   -> Printf.sprintf "{%s}"
                         (String.concat ", " (List.map string_of_field fs))
    | T_view        -> "view"

    | T_set T_empty -> "set<>"
    | T_set t'      -> Printf.sprintf "set<%s>" (string_of_vtype t')

    | T_map (T_empty, T_empty) -> "map<,>"
    | T_map (tk, tv)           -> Printf.sprintf "map<%s,%s>"
                                    (string_of_vtype tk)
                                    (string_of_vtype tv)

(* the runtime type of a value *)
let rec vtype_of (v: value) : vtype =
  let ftype_of (f, fv) = f, vtype_of fv in
  match v with
    | V_unit           -> T_unit
    | V_bool _         -> T_bool
    | V_bit  _         -> T_bit
    | V_char _         -> T_char
    | V_int  _         -> T_int
    | V_float _        -> T_float
    | V_string _       -> T_string
    | V_bitvector _    -> T_bitvector
    | V_bitfield (i,_) -> T_record (List.map (fun (f,_) ->
                                        f, T_bitvector) i.bf_fields)
    | V_option None    -> T_option T_empty
    | V_option (Some o)-> T_option (vtype_of o)
    | V_list []        -> T_list T_empty
    | V_list (e :: _)  -> T_list (vtype_of e)
    | V_tuple vs       -> T_tuple (List.map vtype_of vs)
    | V_constr (c, vs) -> T_adt_constr (c, List.map vtype_of vs)
    | V_record fs      -> T_record (List.map ftype_of fs)
    | V_view _         -> T_view
    | V_set []         -> T_set T_empty
    | V_set (e :: _)   -> T_set (vtype_of e)
    | V_map []         -> T_map (T_empty, T_empty)
    | V_map ((k,v)::_) -> T_map (vtype_of k, vtype_of v)

let field_of_bitvector (v: bool list) (h: int) (l: int) : bool list =
  (* Asserted version of `Builtins.bit_extract`. *)
  let len = List.length v in
  assert (0 <= l && l < len);
  assert (0 <= h && h < len);
  assert (l <= h);
  fst (List.fold_left (fun (acc, idx) b ->
           if   l <= idx && idx <= h
           then b :: acc, idx + 1
           else acc, idx + 1
         ) ([], 0) (List.rev v))

let string_of_value (v: value) : string =
  let rec pr d v =
    let mk_fill d = String.make (2*d + 3) ' ' in
    let mk_sep c  = Printf.sprintf "%s\n %s" c (mk_fill d) in
    let pr_bit b  = if b then "1" else "0" in
    let pr_bvec v =
      Printf.sprintf "0b%s" (String.concat "" (List.map pr_bit v)) in
    let pr_bf v h l = pr_bvec (field_of_bitvector v h l) in
    let srt vl    = List.sort compare vl in
    let srt_r fs  = List.sort (fun (l, _) (r, _) -> compare l r) fs in
    match v with
      | V_unit            -> "()"
      | V_bool b          -> if b then "true" else "false"
      | V_bit  b          -> if b then "1" else "0"
      | V_char c          -> Printf.sprintf "'%s'" (Char.escaped c)
      | V_int  i          -> Int64.to_string i
      | V_float f         -> Float.to_string f
      | V_string s        -> Printf.sprintf "'%s'" s
      | V_bitvector v     -> pr_bvec v
      | V_bitfield (i, v) -> Printf.sprintf "{%s}"
                               (String.concat (mk_sep ";")
                                  (List.map (fun (f, (h, l)) ->
                                       Printf.sprintf "%s: %s" f (pr_bf v h l)
                                     ) (srt_r i.bf_fields)))
      | V_option v        -> (match v with
                                | None   -> "option::None()"
                                | Some v -> Printf.sprintf "option::Some(%s)"
                                              (pr (d + 1) v))
      | V_list vs         -> Printf.sprintf "%s[%s]" (mk_fill d)
                               (String.concat (mk_sep ",") (List.map (pr (d + 1)) vs))
      | V_tuple vs        -> Printf.sprintf "(%s)"
                               (String.concat (mk_sep ",") (List.map (pr (d + 1)) vs))
      | V_constr ((t, c), vs) -> Printf.sprintf "%s(%s)"
                                   (Parsing.AstUtils.canonicalize_dcon t c)
                                   (String.concat (mk_sep ",") (List.map (pr (d + 1)) vs))
      | V_record fs       -> Printf.sprintf "{%s}"
                               (String.concat (mk_sep ";")
                                  (List.map (fun (f, v) ->
                                       Printf.sprintf "%s: %s" f (pr (d + 1) v)
                                     ) (srt_r fs)))
      | V_view _v         -> "view"
      | V_set  vs         -> Printf.sprintf "set<%s>"
                               (String.concat (mk_sep ",") (List.map (pr (d + 1)) (srt vs)))
      | V_map  kvs        -> Printf.sprintf "map<%s>"
                               (String.concat (mk_sep ",")
                                  (List.map (fun (k, v) ->
                                       Printf.sprintf "%s: %s" (pr (d+1) k) (pr (d+1) v)
                                     ) (srt kvs))) in
  pr 0 v
