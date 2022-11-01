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

(* The source of the data in a view. *)
type source =
  | Src_file of string (* unmodified data from file *)
  | Src_transform      (* transformed by user program *)

(* API for the internal representation of a static buffer. *)
module type VIEW_BUF = sig
    type t

    val at: t -> int -> char
    val size: t -> int
  end

(* Buffer with a non-extensible mmap-ed backing buffer. *)
module MmapBuf = struct
  type t =
    (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

  let at (b: t) (idx: int) : char =
    b.{idx}

  let size (b: t) : int =
    Bigarray.Array1.size_in_bytes b
end

(* Buffer with an extensible byte-sequence backing buffer. *)
module BytesBuf = struct
  type t = bytes

  let at (b: t) (idx: int) : char =
    Bytes.get b idx

  let size (b: t) : int =
    Bytes.length b

  let extend (b: t) (suf: t) : t =
    Bytes.cat b suf
end

(* Wrapper to perform dispatch based on underlying representation. *)
type buf =
  | Buf_mmap of MmapBuf.t
  | Buf_bytes of BytesBuf.t

let buf_at (b: buf) (i: int) : char =
  match b with
    | Buf_mmap b  -> MmapBuf.at b i
    | Buf_bytes b -> BytesBuf.at b i

let buf_size (b: buf) : int =
  match b with
    | Buf_mmap b  -> MmapBuf.size b
    | Buf_bytes b -> BytesBuf.size b

let buf_is_refillable = function
  | Buf_mmap _  -> false  (* just re-mmap the full file? *)
  | Buf_bytes _ -> true

let buf_refill (b: buf) (bytes: bytes) : buf =
  match b with
    | Buf_mmap _  -> assert false
    | Buf_bytes b -> Buf_bytes (BytesBuf.extend b bytes)

(* A view is a subrange of a buffer, currently represented by a
   possibly shared fixed-length byte sequence.  It is of two kinds:
   . closed: cannot be extended at the end
   . open:   can be extended by adding data to the end of the view
 *)
type view_kind =
  | VK_open
  | VK_closed

type view =
  {vu_buf:         buf ref;
   vu_source:      source;
   vu_id:          Int64.t; (* unique identifier per view *)
   vu_kind:        view_kind;
   (* All locations below are absolute indices into vu_buf.
      The following invariants are maintained:
      . vu_end is 1 past the last valid read index for the buffer
      . 0 <= vu_start <= vu_ofs <= vu_end
      . it is legal for vu_ofs = vu_end; however, it is illegal to use
        that offset for a read. *)
   vu_start:       int;
   vu_ofs:         int;     (* cursor, i.e. index for next read *)
   mutable vu_end: int}     (* allow lazy dynamic extensions *)

(* Extend the span of a view at the end if possible. *)
let extend_view v : unit =
  match v.vu_kind with
    | VK_closed -> ()
    | VK_open   -> v.vu_end <- buf_size !(v.vu_buf)

(* printing helper *)
let string_of_view v : string =
  Printf.sprintf "view<%s: start=%d, ofs=%d, end=%d>"
    (match v.vu_kind with
         | VK_closed -> "closed"
         | VK_open   -> "open")
    v.vu_start
    v.vu_ofs
    v.vu_end

(* Internal types for bitvectors and binary integers. *)

type signed =
  | S_unsigned
  | S_signed

type endian =
  | E_little
  | E_big

(* The values of the expression language.  Sets and maps have an
   inefficient representation since the Set and Map functors in
   OCaml's stdlib give predicative types, and those in `value` are
   impredicative. *)
type bitfield_info = Typing.TypingEnvironment.bitfield_info
type constr = Anfcfg.Anf.constr
type value =
  | V_unit
  | V_bool of bool
  | V_bit of bool
  | V_char of char (* also used for byte *)
  | V_int of Parsing.Ast.num_t * Int64.t
  | V_float of float
  | V_string of string
  | V_bitvector of bool list                (* big-endian *)
  | V_bitfield of bitfield_info * bool list (* big-endian *)
  | V_option of value option
  | V_list of value list
  | V_tuple of value list
  | V_constr of constr * value list
  | V_record of (string * value) list
  (* module types *)
  | V_view of view
  | V_set of value list
  | V_map of (value * value) list

let empty_record = V_record []

(* A type to describe the runtime type of the value. *)
type vtype =
  | T_empty  (* used for empty options, lists, sets and maps *)
  | T_unit
  | T_bool
  | T_bit
  | T_char
  | T_byte
  | T_int of Parsing.Ast.num_t
  | T_float
  | T_string
  | T_bitvector
  | T_option of vtype
  | T_list of vtype
  | T_tuple of vtype list
  | T_adt of string
  | T_adt_constr of constr * vtype list
  | T_record of (string * vtype) list
  | T_view
  | T_set of vtype
  | T_map of vtype * vtype

let mod_prefix    = Anfcfg.Anf.mod_prefix
let str_of_constr = Anfcfg.Anf.string_of_constr

let safe_map f ls =
  List.rev (List.rev_map f ls)

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
    | T_int n     -> Parsing.Ast.str_of_num_t n
    | T_float     -> "float"
    | T_string    -> "string"
    | T_bitvector -> "bitvector"

    | T_option T_empty -> "option<>"
    | T_option t'      -> Printf.sprintf "option<%s>" (string_of_vtype t')

    | T_list T_empty -> Printf.sprintf "list<>"
    | T_list t'      -> Printf.sprintf "list<%s>" (string_of_vtype t')

    | T_tuple ts    -> "("
                       ^ (String.concat ", " (safe_map string_of_vtype ts))
                       ^ ")"
    | T_adt s       -> s
    | T_adt_constr (c, ts) -> Printf.sprintf "%s(%s)" (str_of_constr c)
                                (String.concat ", " (safe_map string_of_vtype ts))
    | T_record fs   -> Printf.sprintf "{%s}"
                         (String.concat ", " (safe_map string_of_field fs))
    | T_view        -> "view"

    | T_set T_empty -> "set<>"
    | T_set t'      -> Printf.sprintf "set<%s>" (string_of_vtype t')

    | T_map (T_empty, T_empty) -> "map<,>"
    | T_map (tk, tv)           -> Printf.sprintf "map<%s,%s>"
                                    (string_of_vtype tk)
                                    (string_of_vtype tv)

(* The runtime type of a value. *)
let rec vtype_of (v: value) : vtype =
  let ftype_of (f, fv) = f, vtype_of fv in
  match v with
    | V_unit           -> T_unit
    | V_bool _         -> T_bool
    | V_bit  _         -> T_bit
    | V_char _         -> T_char
    | V_int  (n, _)    -> T_int n
    | V_float _        -> T_float
    | V_string _       -> T_string
    | V_bitvector _    -> T_bitvector
    | V_bitfield (i,_) -> T_record (safe_map (fun (f,_) ->
                                        f, T_bitvector) i.bf_fields)
    | V_option None    -> T_option T_empty
    | V_option (Some o)-> T_option (vtype_of o)
    | V_list []        -> T_list T_empty
    | V_list (e :: _)  -> T_list (vtype_of e)
    | V_tuple vs       -> T_tuple (safe_map vtype_of vs)
    | V_constr (c, vs) -> T_adt_constr (c, safe_map vtype_of vs)
    | V_record fs      -> T_record (safe_map ftype_of fs)
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

let string_of_value (as_ascii: bool) (v: value) : string =
  let rec pr d v =
    let mk_fill d = String.make (2*d + 3) ' ' in
    let mk_sep c  = Printf.sprintf "%s\n %s" c (mk_fill d) in
    let pr_bit b  = if b then "1" else "0" in
    let pr_bvec v =
      Printf.sprintf "0b%s" (String.concat "" (safe_map pr_bit v)) in
    let pr_bf v h l = pr_bvec (field_of_bitvector v h l) in
    let srt vl    = List.sort compare vl in
    let srt_r fs  = List.sort (fun (l, _) (r, _) -> compare l r) fs in
    let is_byte b = match b with V_char _ -> true | _ -> false in
    let to_hex c  = if   c < 16
                    then Printf.sprintf "0%x" c
                    else Printf.sprintf "%x"  c in
    let pr_hex l = String.concat ""
                     (safe_map (function
                          | V_char c -> to_hex (Char.code c)
                          | _        -> assert false
                        ) l) in
    let pr_str l = String.of_seq
                     (List.to_seq
                        (safe_map (function
                             | V_char c -> c
                             | _        -> assert false
                           ) l)) in
    match v with
      | V_unit            -> "()"
      | V_bool b          -> if b then "true" else "false"
      | V_bit  b          -> if b then "1" else "0"
      | V_char c          -> Printf.sprintf "'%s'" (Char.escaped c)
      | V_int  (_, i)     -> Printf.sprintf "%s (%#Lx)" (Int64.to_string i) i
      | V_float f         -> Float.to_string f
      | V_string s        -> Printf.sprintf "'%s'" s
      | V_bitvector v     -> pr_bvec v
      | V_bitfield (i, v) -> Printf.sprintf "{%s}"
                               (String.concat (mk_sep ";")
                                  (safe_map (fun (f, (h, l)) ->
                                       Printf.sprintf "%s: %s" f (pr_bf v h l)
                                     ) (srt_r i.bf_fields)))
      | V_option v        -> (match v with
                                | None   -> "option::None()"
                                | Some v -> Printf.sprintf "option::Some(%s)"
                                              (pr (d + 1) v))
      | V_list vs
           when List.for_all is_byte vs
                          -> Printf.sprintf "%s"
                               (if as_ascii then pr_str vs else pr_hex vs)
      | V_list vs         -> Printf.sprintf "%s[%s]" (mk_fill d)
                               (String.concat (mk_sep ",") (safe_map (pr (d + 1)) vs))
      | V_tuple vs        -> Printf.sprintf "(%s)"
                               (String.concat (mk_sep ",") (safe_map (pr (d + 1)) vs))
      | V_constr (c, vs) -> Printf.sprintf "%s(%s)"
                              (str_of_constr c)
                              (String.concat (mk_sep ",") (safe_map (pr (d + 1)) vs))
      | V_record fs       -> Printf.sprintf "{%s}"
                               (String.concat (mk_sep ";")
                                  (safe_map (fun (f, v) ->
                                       Printf.sprintf "%s: %s" f (pr (d + 1) v)
                                     ) (srt_r fs)))
      | V_view v          -> string_of_view v
      | V_set  vs         -> Printf.sprintf "set<%s>"
                               (String.concat (mk_sep ",") (safe_map (pr (d + 1)) (srt vs)))
      | V_map  kvs        -> Printf.sprintf "map<%s>"
                               (String.concat (mk_sep ",")
                                  (safe_map (fun (k, v) ->
                                       Printf.sprintf "%s: %s" (pr (d+1) k) (pr (d+1) v)
                                     ) (srt kvs))) in
  pr 0 v
