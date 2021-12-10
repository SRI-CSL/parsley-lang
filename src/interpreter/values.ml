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

   (* all locations below are maintained wrt to the start of vu_buf *)
   vu_start:  int;
   vu_ofs:    int;     (* cursor *)
   vu_end:    int}

(* the values of the expression language.  sets and maps have an
   inefficient representation since the Set and Map functors in
   OCaml's stdlib give predicative types, and those in `value` are
   impredicative. *)
type value =
  | V_unit
  | V_bool of bool
  | V_bit of bool
  | V_char of char (* also used for byte *)
  | V_int of Int64.t
  | V_float of float
  | V_string of string
  | V_bitvector of bool list
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
  | T_adt of (string * string) * vtype list
  | T_record of (string * vtype) list
  | T_view
  | T_set of vtype
  | T_map of vtype * vtype

let rec string_of_vtype t =
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
    | T_adt ((t', c), ts) -> Printf.sprintf "%s::%s(%s)" t' c
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
let rec vtype_of v =
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
    | V_option None    -> T_option T_empty
    | V_option (Some o)-> T_option (vtype_of o)
    | V_list []        -> T_list T_empty
    | V_list (e :: _)  -> T_list (vtype_of e)
    | V_tuple vs       -> T_tuple (List.map vtype_of vs)
    | V_constr (c, vs) -> T_adt (c, List.map vtype_of vs)
    | V_record fs      -> T_record (List.map ftype_of fs)
    | V_view _         -> T_view
    | V_set []         -> T_set T_empty
    | V_set (e :: _)   -> T_set (vtype_of e)
    | V_map []         -> T_map (T_empty, T_empty)
    | V_map ((k,v)::_) -> T_map (vtype_of k, vtype_of v)
