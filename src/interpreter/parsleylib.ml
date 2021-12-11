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

(* The standard library for Parsley *)

open Values
open Runtime_exceptions
open Internal_errors

(* Please ensure that the modules and functions below follow the order
   in typeAlgebra.ml.  The modules use the 'P' prefix to avoid
   colliding with any OCaml libraries with the same name. *)

module PInt = struct
  let of_byte lc (v: value) : value =
    match v with
      | V_char c -> V_int (Int64.of_int (Char.code c))
      | _ -> internal_error (Type_error (lc, "Int.of_byte", 1, vtype_of v, T_byte))

  let of_string lc (v: value) : value =
    match v with
      | V_string s -> (match int_of_string_opt s with
                         | Some i -> V_option (Some (V_int (Int64.of_int i)))
                         | None   -> V_option None)
      | _ -> internal_error (Type_error (lc, "Int.of_string", 1, vtype_of v, T_string))

  let of_bytes lc (v: value) : value =
    let err =
      Type_error (lc, "Int.of_bytes", 1, vtype_of v, T_list T_byte) in
    let conv v =
      match v with
        | V_char c -> c
        | _ -> internal_error err in
    match v with
      | V_list l ->
          let cs = List.map conv l in
          let buf = Buffer.create 16 in
          List.iter (Buffer.add_char buf) cs;
          of_string lc (V_string (Buffer.contents buf))
      | _ ->
          internal_error err

  let of_bytes_unsafe lc (v: value) : value =
    match of_bytes lc v with
      | V_option None ->
          fault (Unsafe_operation_failure (lc, "Int.of_bytes_unsafe"))
      | V_option (Some i) ->
          i
      | _ ->
          assert false
end

module PList = struct
  let head lc (v: value) : value =
    match v with
      | V_list [] -> fault (Invalid_argument (lc, "List.head", "0-length list"))
      | V_list (h :: _) -> h
      | _ -> internal_error (Type_error (lc, "List.head", 1, vtype_of v, T_list T_empty))

  let tail lc (v: value) : value =
    match v with
      | V_list [] -> fault (Invalid_argument (lc, "List.tail", "0-length list"))
      | V_list (h :: _) -> h
      | _ -> internal_error (Type_error (lc, "List.tail", 1, vtype_of v, T_list T_empty))

  let length lc (v: value) : value =
    match v with
      | V_list l -> V_int (Int64.of_int (List.length l))
      | _ -> internal_error (Type_error (lc, "List.length", 1, vtype_of v, T_list T_empty))

  let cons lc (l: value) (r: value) : value =
    match r with
      | V_list r ->
          V_list (l :: r)
      | _ ->
          internal_error (Type_error (lc, "List.cons", 2, vtype_of r, T_list T_empty))

  let concat lc (l: value) (r: value) : value =
    match l, r with
      | V_list l, V_list r ->
          V_list (l @ r)
      | V_list _, _ ->
          internal_error (Type_error (lc, "List.concat", 2, vtype_of r, T_list T_empty))
      | _, _ ->
          internal_error (Type_error (lc, "List.concat", 1, vtype_of l, T_list T_empty))

  let index lc (l: value) (r: value) : value =
    match l, r with
      | V_list l, V_int r ->
        (* FIXME: this conversion is lossy on 32-bit platforms and
           hence a source of bugs.  This should be addressed via a
           resource bound mechanism, that ensures that list sizes
           don't exceed platform-specific representable bounds.
           Indices should be compared against these bounds before
           conversion. *)
          let idx = Int64.to_int r in
          (match List.nth_opt l idx with
             | None   -> V_option None
             | Some v -> V_option (Some v))
      | V_list _, _ ->
          internal_error (Type_error (lc, "List.index", 2, vtype_of r, T_int))
      | _, _ ->
          internal_error (Type_error (lc, "List.index", 1, vtype_of l, T_list T_empty))

  let flatten lc (v: value) : value =
    let exp_t = T_list (T_list T_empty) in
    let err = Type_error (lc, "List.flatten", 1, vtype_of v, exp_t) in
    let conv e = match e with
        | V_list e -> e
        | _ -> internal_error err in
    match v with
      | V_list l -> let l' = List.map conv l in
                    V_list (List.concat l')
      | _ -> internal_error err

  let rev lc (v: value) : value =
    match v with
      | V_list l -> V_list (List.rev l)
      | _ -> internal_error (Type_error (lc, "List.rev", 1, vtype_of v, T_list T_empty))

  let repl lc (v: value) (i: value) : value =
    match i with
      | V_int i when Int64.compare i Int64.zero < 0 ->
          fault (Invalid_argument (lc, "List.repl", "count is negative"))
      | V_int i ->
          (* TODO: resource bound check on i *)
          let l = List.init (Int64.to_int i) (fun _ -> v) in
          V_list l
      | _ ->
          internal_error (Type_error (lc, "List.repl", 2, vtype_of i, T_int))

  (* Higher order functions (e.g. `map` and `map2`) are implemented
     via macro-like code-generation. *)
end

module PString = struct
  let empty _lc : value =
    V_string ""

  let concat lc (l: value) (r: value) : value =
    match l, r with
      | V_string l, V_string r ->
          V_string (l ^ r)
      | V_string _, _ ->
          internal_error (Type_error (lc, "String.concat", 2, vtype_of r, T_string))
      | _, _ ->
          internal_error (Type_error (lc, "String.concat", 1, vtype_of l, T_string))

  let to_int lc (v: value) : value =
    match v with
      | V_string s -> (match int_of_string_opt s with
                         | Some i -> V_option (Some (V_int (Int64.of_int i)))
                         | None   -> V_option None)
      | _ -> internal_error (Type_error (lc, "String.to_int", 1, vtype_of v, T_string))

  let to_bytes lc (v: value) : value =
    match v with
      | V_string s ->
          let len = String.length s in
          let rec mk acc i =
            if i < 0 then acc else mk (V_char s.[i] :: acc) (i - 1) in
          V_list (mk [] (len - 1))
      | _ ->
          internal_error (Type_error (lc, "String.to_bytes", 1, vtype_of v, T_string))

  (* no character set support yet, so bytes and characters are currently equivalent *)

  let of_bytes lc (v: value) : value =
    let exp_t = T_list T_byte in
    let err = Type_error (lc, "String.of_bytes", 1, vtype_of v, exp_t) in
    let conv v =
      match v with
        | V_char c -> c
        | _ -> internal_error err in
    match v with
      | V_list l ->
          let l = List.map conv l in
          let buf = Buffer.create 16 in
          List.iter (Buffer.add_char buf) l;
          V_option (Some (V_string (Buffer.contents buf)))
      | _ ->
          internal_error err

  let of_bytes_unsafe lc (v: value) : value =
    match of_bytes lc v with
      | V_option None ->
          fault (Unsafe_operation_failure (lc, "String.of_bytes_unsafe"))
      | V_option (Some s) ->
          s
      | _ ->
          assert false

  let of_literal lc (v: value) : value =
    match v with
      | V_string _ ->
          v
      | _ ->
          internal_error (Type_error (lc, "String.of_literal", 1, vtype_of v, T_string))
end

module PBits = struct
  let to_uint lc (v: value) : value =
    match v with
      | V_bitvector [] ->
          fault (Invalid_argument (lc, "Bits.to_uint", "0-length bitvector"))
      | V_bitvector bs ->
          let i, _ =
            List.fold_left (fun (i, cnt) b ->
                if cnt >= 64
                then fault (Overflow (lc, "Bits.to_uint"))
                else let i = Int64.shift_left i 1 in
                     let b = if b then Int64.one else Int64.zero in
                     Int64.logor i b, cnt + 1
              ) (Int64.zero, 0) (List.rev bs) in
          V_int i
      | _ ->
          internal_error (Type_error (lc, "Bits.to_uint", 1, vtype_of v, T_bitvector))

  let to_int lc (v: value) : value =
    match v with
      | V_bitvector [] ->
          fault (Invalid_argument (lc, "Bits.to_int", "0-length bitvector"))

      (* TODO: it is probably wrong to always assume that the
       * top-most width is the sign bit. *)
      | V_bitvector (s :: bs) ->
          let i, _ =
            List.fold_left (fun (i, cnt) b ->
                if cnt >= 63
                then fault (Overflow (lc, "Bits.to_int"))
                else let i = Int64.shift_left i 1 in
                     let b = if b then Int64.one else Int64.zero in
                     Int64.logor i b, cnt + 1
              ) (Int64.zero, 0) (List.rev bs) in
          V_int (if s then Int64.neg i else i)

      | _ ->
          internal_error (Type_error (lc, "Bits.to_int", 1, vtype_of v, T_bitvector))

  let to_bool lc (v: value) : value =
    match v with
      | V_bit b -> V_bool b
      | _ -> internal_error (Type_error (lc, "Bits.to_bool", 1, vtype_of v, T_bit))

  let of_bool lc (v: value) : value =
    match v with
      | V_bool b -> V_bit b
      | _ -> internal_error (Type_error (lc, "Bits.of_bool", 1, vtype_of v, T_bool))

  let to_bit lc (v: value) : value =
    match v with
      | V_bitvector [b] ->
          V_bit b
      | V_bitvector bs  ->
          let m = Printf.sprintf "%d-length bitvector" (List.length bs) in
          fault (Invalid_argument (lc, "Bits.to_bit", m))
      | _ ->
          internal_error (Type_error (lc, "Bits.to_bit", 1, vtype_of v, T_bitvector))

  let of_bit lc (v: value) : value =
    match v with
      | V_bit b -> V_bitvector [b]
      | _ -> internal_error (Type_error (lc, "Bits.of_bit", 1, vtype_of v, T_bit))

  let mk_bv lc op len v =
    (* TODO: resource bound check on len *)
    if Int64.compare len Int64.zero >= 0
    then V_bitvector (List.init (Int64.to_int len) (fun _ -> v))
    else fault (Invalid_argument (lc, op, "negative size"))

  let ones lc (v: value) : value =
    match v with
      | V_int i ->
          mk_bv lc "Bits.ones" i true
      | _ ->
          internal_error (Type_error (lc, "Bits.ones", 1, vtype_of v, T_int))

  let zeros lc (v: value) : value =
    match v with
      | V_int i ->
          mk_bv lc "Bits.zeros" i false
      | _ ->
          internal_error (Type_error (lc, "Bits.zeros", 1, vtype_of v, T_int))
end

module VSet = Set.Make(struct type t = value
                              let compare = compare
                       end)
module PSet = struct
  let empty _lc : value =
    V_list []

  let add lc (v: value) (e: value) : value =
    match v with
      | V_set [] ->
          V_set [e]
      | V_set ((se :: _) as vs) ->
          let etyp = vtype_of e in
          let setyp = vtype_of se in
          (* This can be expensive but can be turned off after initial testing *)
          if List.exists (fun se -> vtype_of se != setyp) vs
          then assert false;
          if setyp != etyp
          then internal_error (Type_error (lc, "Set.add", 2, etyp, setyp));
          let set = VSet.of_list vs in
          V_set (VSet.elements (VSet.add e set))
      | _ ->
          internal_error (Type_error (lc, "Set.add", 1, vtype_of v, T_set T_empty))

  let mem lc (v: value) (e: value) : value =
    match v with
      | V_set [] ->
          V_bool false
      | V_set ((se :: _) as vs) ->
          let etyp = vtype_of e in
          let setyp = vtype_of se in
          (* This can be expensive but can be turned off after initial testing *)
          if List.exists (fun se -> vtype_of se != setyp) vs
          then assert false;
          if setyp != etyp
          then internal_error (Type_error (lc, "Set.mem", 2, etyp, setyp));
          let set = VSet.of_list vs in
          V_bool (VSet.mem e set)
      | _ ->
          internal_error (Type_error (lc, "Set.mem", 1, vtype_of v, T_set T_empty))
end

module VMap = Map.Make(struct type t = value
                              let compare = compare
                       end)
module PMap = struct
  let empty _lc : value =
    V_map []

  let add lc (m: value) (k: value) (v: value) : value =
    match m with
      | V_map [] ->
          V_map [k, v]
      | V_map (((mk, mv) :: _) as kvs) ->
          let mktyp, mvtyp = vtype_of mk, vtype_of mv in
          let ktyp, vtyp   = vtype_of k, vtype_of v in
          let ks, vs = List.split kvs in
          (* This can be expensive but can be turned off after initial testing *)
          if List.exists (fun ke -> vtype_of ke != mktyp) ks
          then assert false;
          if List.exists (fun ve -> vtype_of ve != mvtyp) vs
          then assert false;
          if mktyp != ktyp
          then internal_error (Type_error (lc, "Map.add", 2, ktyp, mktyp));
          if mvtyp != vtyp
          then internal_error (Type_error (lc, "Map.add", 3, vtyp, mvtyp));
          let map = VMap.of_seq (List.to_seq kvs) in
          let map = VMap.add k v map in
          V_map (List.of_seq (VMap.to_seq map))
      | _ ->
          let exp_t = T_map (vtype_of k, vtype_of v) in
          internal_error (Type_error (lc, "Map.add", 1, vtype_of m, exp_t))

  let mem lc (m: value) (k: value) : value =
    match m with
      | V_map [] ->
          V_bool false
      | V_map (((mk, mv) :: _) as kvs) ->
          let mktyp, mvtyp = vtype_of mk, vtype_of mv in
          let ktyp = vtype_of k in
          let ks, vs = List.split kvs in
          (* This can be expensive but can be turned off after initial testing *)
          if List.exists (fun ke -> vtype_of ke != mktyp) ks
          then assert false;
          if List.exists (fun ve -> vtype_of ve != mvtyp) vs
          then assert false;
          if mktyp != ktyp
          then internal_error (Type_error (lc, "Map.mem", 2, ktyp, mktyp));
          let map = VMap.of_seq (List.to_seq kvs) in
          V_bool (VMap.mem k map)
      | _ ->
          let exp_t = T_map (vtype_of k, T_empty) in
          internal_error (Type_error (lc, "Map.mem", 1, vtype_of m, exp_t))

  let find lc (m: value) (k: value) : value =
    match m with
      | V_map [] ->
          V_option None
      | V_map (((mk, mv) :: _) as kvs) ->
          let mktyp, mvtyp = vtype_of mk, vtype_of mv in
          let ktyp = vtype_of k in
          let ks, vs = List.split kvs in
          (* This can be expensive but can be turned off after initial testing *)
          if List.exists (fun ke -> vtype_of ke != mktyp) ks
          then assert false;
          if List.exists (fun ve -> vtype_of ve != mvtyp) vs
          then assert false;
          if mktyp != ktyp
          then internal_error (Type_error (lc, "Map.find", 2, ktyp, mktyp));
          let map = VMap.of_seq (List.to_seq kvs) in
          V_option (VMap.find_opt k map)
      | _ ->
          let exp_t = T_map (vtype_of k, T_empty) in
          internal_error (Type_error (lc, "Map.find", 1, vtype_of m, exp_t))

  let find_unsafe lc (m: value) (k: value) : value =
    match find lc m k with
      | V_option None ->
          fault (Unsafe_operation_failure (lc, "Map.find_unsafe"))
      | V_option (Some v) ->
          v
      | _ ->
          assert false
end

module PView = struct
  (* incremented and used as id for every new view value created *)
  let view_id = ref Int64.zero

  let next_id () =
    let id = !view_id in
    view_id := Int64.succ !view_id;
    id

  let restrict lc (v: value) (o: value) (l: value) : value =
    match v, o, l with
      | V_view v, V_int o, V_int l ->
          if Int64.compare o Int64.zero < 0
          then fault (Invalid_argument (lc, "View.restrict", "negative offset"))
          else if Int64.compare l Int64.zero < 0
          then fault (Invalid_argument (lc, "View.restrict", "negative length"))
          else begin
              assert (0 <= v.vu_start && v.vu_start <= v.vu_ofs);
              assert (v.vu_ofs <= v.vu_end);
              assert (v.vu_end <= ViewBuf.size v.vu_buf);
              let o, l = Int64.to_int o, Int64.to_int l in
              if v.vu_ofs + o + l >= v.vu_end
              then fault (View_bound (lc, "View.restrict", "end bound exceeded"))
              else V_view {v with vu_id    = next_id ();
                                  vu_start = v.vu_ofs + o;
                                  vu_ofs   = 0;
                                  vu_end   = v.vu_ofs + o + l}
            end
      | V_view _, V_int _, _ ->
          internal_error (Type_error (lc, "View.restrict", 3, vtype_of l, T_int))
      | V_view _, _, _ ->
          internal_error (Type_error (lc, "View.restrict", 2, vtype_of o, T_int))
      | _, _, _ ->
          internal_error (Type_error (lc, "View.restrict", 1, vtype_of v, T_view))

  let restrict_from lc (v: value) (o: value) : value =
    match v, o with
      | V_view v, V_int o ->
          if Int64.compare o Int64.zero < 0
          then fault (Invalid_argument (lc, "View.restrict_from", "negative offset"))
          else begin
              assert (0 <= v.vu_start && v.vu_start <= v.vu_ofs);
              assert (v.vu_ofs <= v.vu_end);
              assert (v.vu_end <= ViewBuf.size v.vu_buf);
              let o = Int64.to_int o in
              if   v.vu_ofs + o >= v.vu_end
              then fault (View_bound (lc, "View.restrict_from", "end bound exceeded"))
              else V_view {v with vu_id    = next_id ();
                                  vu_start = v.vu_ofs;
                                  vu_ofs   = 0}
            end
      | V_view _, _ ->
          internal_error (Type_error (lc, "View.restrict_from", 2, vtype_of o, T_int))
      | _, _ ->
          internal_error (Type_error (lc, "View.restrict_from", 1, vtype_of v, T_view))

  let clone lc (v: value) : value =
    match v with
      | V_view v ->
          V_view {vu_buf    = v.vu_buf;
                  vu_source = v.vu_source;
                  vu_id     = next_id ();
                  vu_start  = v.vu_start;
                  vu_ofs    = v.vu_ofs;
                  vu_end    = v.vu_end}
      | _ ->
          internal_error (Type_error (lc, "View.clone", 1, vtype_of v, T_view))

  (* Functions that access interpreter state need to be handled
     directly by the interpreter *)
  let get_base lc _ : value =
    internal_error (Not_implemented (lc, "View.get_base"))

  let get_current lc _ : value =
    internal_error (Not_implemented (lc, "View.get_current"))

  let get_current_cursor lc _ : value =
    internal_error (Not_implemented (lc, "View.get_current_cursor"))
end
