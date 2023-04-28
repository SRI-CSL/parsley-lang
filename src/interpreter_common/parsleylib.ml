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

open Parsing
open Values
open Runtime_exceptions
open Fi
open Internal_errors

(* common helpers *)

let cond lc (v: value) : bool =
  match v with
    | V_bool b -> b
    | _ -> internal_error lc (Type_error ("cond", 1, vtype_of v, T_bool))

let endian_of (v: value) : endian option =
  match v with
    | V_constr (_, l) when List.length l > 0 ->
        None
    | V_constr ((Anf_common.M_stdlib, t, c), _) when t = "endian" && c = "Big" ->
        Some E_big
    | V_constr ((Anf_common.M_stdlib, t, c), _) when t = "endian" && c = "Little" ->
        Some E_little
    | _ ->
        None

(* Please ensure that the modules and functions below follow the order
   in typeAlgebra.ml.  The modules use the 'P' prefix to avoid
   colliding with any OCaml libraries with the same name. *)

module PByte = struct
  let of_int_checked ta lc (v: value) : value =
    let ts = Ast.str_of_num_t ta in
    let fn = "Byte.of_" ^ ts in
    match v with
      | V_int (ti, i)
           when ta = ti && Builtins.check_int_bounds Ast.u8_t i ->
          V_option (Some (V_char (Char.chr (Int64.to_int i))))
      | V_int (ti, _) when ta = ti ->
          V_option None
      | _ ->
          internal_error lc (Type_error (fn, 1, vtype_of v, T_int ta))

  let of_int_wrapped t lc (v: value) : value =
    let ts = Ast.str_of_num_t t in
    let fn = "Byte.of_" ^ ts ^ "_wrapped" in
    match v with
      | V_int (ti, i) when t = ti ->
          let c = Int64.unsigned_rem i 256L in
          V_char (Char.chr (Int64.to_int c))
      | _ ->
          internal_error lc (Type_error (fn, 1, vtype_of v, T_int t))

  let to_int t lc (v: value) : value =
    let ts = Ast.str_of_num_t t in
    let fn = "Byte.to_" ^ ts in
    match v with
      | V_char c when t = (Ast.S_signed, Ast.NW_8) ->
          (* handle wraparound for i8_t *)
          let i = Char.code c in
          let i = if i > 127 then i - 256 else i in
          V_int (t, Int64.of_int i)
      | V_char c ->
          V_int (t, Int64.of_int (Char.code c))
      | _ ->
          internal_error lc (Type_error (fn, 1, vtype_of v, T_char))

  module Byte : PARSLEY_MOD = struct
    let name = "Byte"

    let arg0_funcs = []
    let arg1_funcs = [
        "of_i8",              of_int_checked Ast.i8_t;
        "of_u8",              of_int_checked Ast.u8_t;
        "of_i16",             of_int_checked Ast.i16_t;
        "of_u16",             of_int_checked Ast.u16_t;
        "of_i32",             of_int_checked Ast.i32_t;
        "of_u32",             of_int_checked Ast.u32_t;
        "of_i64",             of_int_checked Ast.i64_t;
        "of_u64",             of_int_checked Ast.u64_t;
        "of_isize",           of_int_checked Ast.isize_t;
        "of_usize",           of_int_checked Ast.usize_t;

        "of_i8_wrapped",      of_int_wrapped Ast.i8_t;
        "of_u8_wrapped",      of_int_wrapped Ast.u8_t;
        "of_i16_wrapped",     of_int_wrapped Ast.i16_t;
        "of_u16_wrapped",     of_int_wrapped Ast.u16_t;
        "of_i32_wrapped",     of_int_wrapped Ast.i32_t;
        "of_u32_wrapped",     of_int_wrapped Ast.u32_t;
        "of_i64_wrapped",     of_int_wrapped Ast.i64_t;
        "of_u64_wrapped",     of_int_wrapped Ast.u64_t;
        "of_isize_wrapped",   of_int_wrapped Ast.isize_t;
        "of_usize_wrapped",   of_int_wrapped Ast.usize_t;
      ]
    let arg2_funcs = []
    let arg3_funcs = []
  end
end

(* This module implements all the various stdlib modules for the
   various integer types.  The `tm` argument indicates the type
   implemented by the module. *)
module PInt = struct
  let of_byte tm lc (v: value) : value =
    let ms = String.uppercase_ascii (Ast.str_of_num_t tm) in
    let fn = ms ^ ".of_byte" in
    match v with
      | V_char c when tm = (Ast.S_signed, Ast.NW_8) ->
          (* handle wraparound for i8_t *)
          let i = Char.code c in
          let i = if i > 127 then i - 256 else i in
          V_int (tm, Int64.of_int i)
      | V_char c ->
          V_int (tm, Int64.of_int (Char.code c))
      | _ -> internal_error lc (Type_error (fn, 1, vtype_of v, T_int tm))

  let of_string tm lc (v: value) : value =
    let ms = String.uppercase_ascii (Ast.str_of_num_t tm) in
    let fn = ms ^ ".of_string" in
    match v with
      | V_string s ->
          (match int_of_string_opt s with
             | Some i ->
                 let i = Int64.of_int i in
                 if   Builtins.check_int_bounds tm i
                 then V_option (Some (V_int (tm, i)))
                 else V_option None
             | _ ->
                 V_option None)
      | _ -> internal_error lc (Type_error (fn, 1, vtype_of v, T_string))

  let of_string_unsafe tm lc (v: value) : value =
    let ms = String.uppercase_ascii (Ast.str_of_num_t tm) in
    let fn = ms ^ ".of_string_unsafe" in
    (* FIXME: on type errors, the error message comes from `of_string`
       instead of `of_string_unsafe`. *)
    match of_string tm lc v with
      | V_option None ->
          fault lc (Unsafe_operation_failure fn)
      | V_option (Some v) ->
          v
      | _ ->
          assert false

  let of_bytes tm lc (v: value) : value =
    let ms  = String.uppercase_ascii (Ast.str_of_num_t tm) in
    let fn  = ms ^ ".of_bytes" in
    let err = Type_error (fn, 1, vtype_of v, T_list T_byte) in
    let conv v =
      match v with
        | V_char c -> c
        | _ -> internal_error lc err in
    match v with
      | V_list l ->
          let cs = safe_map conv l in
          (* This assumes big-endian; i.e. leading byte is most
             significant.  FIXME: should we parameterize by
             endianness? *)
          let max_bytes = (Builtins.get_width tm) / 8 in
          (* Allow conversion from byte-vectors of shorter lengths
             since they cannot overflow. *)
          if   max_bytes < List.length cs
          then V_option None
          else let i =
                 List.fold_left (fun i b ->
                     let i = Int64.shift_left i 8 in
                     Int64.logor i (Int64.of_int (Char.code b))
                   ) 0L cs in
               let i = Builtins.wrap_int_bounds tm i in
               V_option (Some (V_int (tm, i)))
      | _ ->
          internal_error lc err

  let of_bytes_unsafe tm lc (v: value) : value =
    let ms = String.uppercase_ascii (Ast.str_of_num_t tm) in
    let fn = ms ^ ".of_bytes_unsafe" in
    (* FIXME: on type errors, the error message comes from `of_bytes`
       instead of `of_bytes_unsafe`. *)
    match of_bytes tm lc v with
      | V_option None ->
          fault lc (Unsafe_operation_failure fn)
      | V_option (Some i) ->
          i
      | _ ->
          assert false

  (* These functions implement all the integer conversions for the
     integer module.  The `ta` argument indicates the expected source
     integer type. *)

  let of_int_wrapped tm ta lc (v: value) : value =
    (* wrapped conversions *)
    let ms = String.uppercase_ascii (Ast.str_of_num_t tm) in
    let fn = ms ^ ".of_" ^ Ast.str_of_num_t ta ^ "_wrapped" in
    match v with
      | V_int (ti, i) when ti = ta ->
          let i = Builtins.wrap_int_bounds tm i in
          V_int (tm, i)
      | _ ->
          internal_error lc (Type_error (fn, 1, vtype_of v, T_int ta))

  let of_int tm ta lc (v: value) : value =
    let ms = String.uppercase_ascii (Ast.str_of_num_t tm) in
    let fn = ms ^ ".of_" ^ Ast.str_of_num_t ta ^ "_safe" in
    match v with
      | V_int (ti, i) when ti = ta ->
          V_option (if   Builtins.check_int_bounds tm i
                    then Some (V_int (tm, i))
                    else None)
      | _ ->
          internal_error lc (Type_error (fn, 1, vtype_of v, T_int ta))

  module I8 : PARSLEY_MOD = struct
    let name = "I8"
    let arg0_funcs = []
    let arg1_funcs = [
        "of_byte",              of_byte   Ast.i8_t;
        "of_string",            of_string Ast.i8_t;
        "of_string_unsafe",     of_string_unsafe Ast.i8_t;

        "of_i16",               of_int Ast.i8_t Ast.i16_t;
        "of_i32",               of_int Ast.i8_t Ast.i32_t;
        "of_i64",               of_int Ast.i8_t Ast.i64_t;
        "of_isize",             of_int Ast.i8_t Ast.isize_t;
        "of_u8",                of_int Ast.i8_t Ast.u8_t;
        "of_u16",               of_int Ast.i8_t Ast.u16_t;
        "of_u32",               of_int Ast.i8_t Ast.u32_t;
        "of_u64",               of_int Ast.i8_t Ast.u64_t;
        "of_usize",             of_int Ast.i8_t Ast.usize_t;

        "of_i16_wrapped",       of_int_wrapped Ast.i8_t Ast.i16_t;
        "of_i32_wrapped",       of_int_wrapped Ast.i8_t Ast.i32_t;
        "of_i64_wrapped",       of_int_wrapped Ast.i8_t Ast.i64_t;
        "of_isize_wrapped",     of_int_wrapped Ast.i8_t Ast.isize_t;
        "of_u8_wrapped",        of_int_wrapped Ast.i8_t Ast.u8_t;
        "of_u16_wrapped",       of_int_wrapped Ast.i8_t Ast.u16_t;
        "of_u32_wrapped",       of_int_wrapped Ast.i8_t Ast.u32_t;
        "of_u64_wrapped",       of_int_wrapped Ast.i8_t Ast.u64_t;
        "of_usize_wrapped",     of_int_wrapped Ast.i8_t Ast.usize_t;
      ]
    let arg2_funcs = []
    let arg3_funcs = []
  end
  module U8 : PARSLEY_MOD = struct
    let name = "U8"
    let arg0_funcs = []
    let arg1_funcs = [
        "of_byte",              of_byte   Ast.u8_t;
        "of_string",            of_string Ast.u8_t;
        "of_string_unsafe",     of_string_unsafe Ast.u8_t;

        "of_i8",                of_int Ast.u8_t Ast.i8_t;
        "of_i16",               of_int Ast.u8_t Ast.i16_t;
        "of_i32",               of_int Ast.u8_t Ast.i32_t;
        "of_i64",               of_int Ast.u8_t Ast.i64_t;
        "of_isize",             of_int Ast.u8_t Ast.isize_t;
        "of_u16",               of_int Ast.u8_t Ast.u16_t;
        "of_u32",               of_int Ast.u8_t Ast.u32_t;
        "of_u64",               of_int Ast.u8_t Ast.u64_t;
        "of_usize",             of_int Ast.u8_t Ast.usize_t;

        "of_i8_wrapped",        of_int_wrapped Ast.u8_t Ast.i8_t;
        "of_i16_wrapped",       of_int_wrapped Ast.u8_t Ast.i16_t;
        "of_i32_wrapped",       of_int_wrapped Ast.u8_t Ast.i32_t;
        "of_i64_wrapped",       of_int_wrapped Ast.u8_t Ast.i64_t;
        "of_isize_wrapped",     of_int_wrapped Ast.u8_t Ast.isize_t;
        "of_u16_wrapped",       of_int_wrapped Ast.u8_t Ast.u16_t;
        "of_u32_wrapped",       of_int_wrapped Ast.u8_t Ast.u32_t;
        "of_u64_wrapped",       of_int_wrapped Ast.u8_t Ast.u64_t;
        "of_usize_wrapped",     of_int_wrapped Ast.u8_t Ast.usize_t;
      ]
    let arg2_funcs = []
    let arg3_funcs = []
  end
  module I16 : PARSLEY_MOD = struct
    let name = "I16"
    let arg0_funcs = []
    let arg1_funcs = [
        "of_byte",             of_byte   Ast.i16_t;
        "of_string",           of_string Ast.i16_t;
        "of_bytes",            of_bytes  Ast.i16_t;
        "of_string_unsafe",    of_string_unsafe Ast.i16_t;
        "of_bytes_unsafe",     of_bytes_unsafe  Ast.i16_t;

        "of_i8",               of_int_wrapped Ast.i16_t Ast.i8_t;
        "of_i32",              of_int Ast.i16_t Ast.i32_t;
        "of_i64",              of_int Ast.i16_t Ast.i64_t;
        "of_isize",            of_int Ast.i16_t Ast.isize_t;
        "of_u8",               of_int_wrapped Ast.i16_t Ast.u8_t;
        "of_u16",              of_int Ast.i16_t Ast.u16_t;
        "of_u32",              of_int Ast.i16_t Ast.u32_t;
        "of_u64",              of_int Ast.i16_t Ast.u64_t;
        "of_usize",            of_int Ast.i16_t Ast.usize_t;

        "of_i32_wrapped",      of_int_wrapped Ast.i16_t Ast.i32_t;
        "of_i64_wrapped",      of_int_wrapped Ast.i16_t Ast.i64_t;
        "of_isize_wrapped",    of_int_wrapped Ast.i16_t Ast.isize_t;
        "of_u16_wrapped",      of_int_wrapped Ast.i16_t Ast.u16_t;
        "of_u32_wrapped",      of_int_wrapped Ast.i16_t Ast.u32_t;
        "of_u64_wrapped",      of_int_wrapped Ast.i16_t Ast.u64_t;
        "of_usize_wrapped",    of_int_wrapped Ast.i16_t Ast.usize_t;
      ]
    let arg2_funcs = []
    let arg3_funcs = []
  end
  module U16 : PARSLEY_MOD = struct
    let name = "U16"
    let arg0_funcs = []
    let arg1_funcs = [
        "of_byte",             of_byte   Ast.u16_t;
        "of_string",           of_string Ast.u16_t;
        "of_bytes",            of_bytes  Ast.u16_t;
        "of_string_unsafe",    of_string_unsafe Ast.u16_t;
        "of_bytes_unsafe",     of_bytes_unsafe  Ast.u16_t;

        "of_i8",               of_int Ast.u16_t Ast.i8_t;
        "of_i16",              of_int Ast.u16_t Ast.i16_t;
        "of_i32",              of_int Ast.u16_t Ast.i32_t;
        "of_i64",              of_int Ast.u16_t Ast.i64_t;
        "of_isize",            of_int Ast.u16_t Ast.isize_t;
        "of_u8",               of_int_wrapped Ast.u16_t Ast.u8_t;
        "of_u32",              of_int Ast.u16_t Ast.u32_t;
        "of_u64",              of_int Ast.u16_t Ast.u64_t;
        "of_usize",            of_int Ast.u16_t Ast.usize_t;

        "of_i8_wrapped",       of_int_wrapped Ast.u16_t Ast.i8_t;
        "of_i16_wrapped",      of_int_wrapped Ast.u16_t Ast.i16_t;
        "of_i32_wrapped",      of_int_wrapped Ast.u16_t Ast.i32_t;
        "of_i64_wrapped",      of_int_wrapped Ast.u16_t Ast.i64_t;
        "of_isize_wrapped",    of_int_wrapped Ast.u16_t Ast.isize_t;
        "of_u32_wrapped",      of_int_wrapped Ast.u16_t Ast.u32_t;
        "of_u64_wrapped",      of_int_wrapped Ast.u16_t Ast.u64_t;
        "of_usize_wrapped",    of_int_wrapped Ast.u16_t Ast.usize_t;
      ]
    let arg2_funcs = []
    let arg3_funcs = []
  end
  module I32 : PARSLEY_MOD = struct
    let name = "I32"
    let arg0_funcs = []
    let arg1_funcs = [
        "of_byte",             of_byte   Ast.i32_t;
        "of_string",           of_string Ast.i32_t;
        "of_bytes",            of_bytes  Ast.i32_t;
        "of_string_unsafe",    of_string_unsafe Ast.i32_t;
        "of_bytes_unsafe",     of_bytes_unsafe  Ast.i32_t;

        "of_i8",               of_int_wrapped Ast.i32_t Ast.i8_t;
        "of_i16",              of_int_wrapped Ast.i32_t Ast.i16_t;
        "of_i64",              of_int Ast.i32_t Ast.i64_t;
        "of_isize",            of_int Ast.i32_t Ast.isize_t;
        "of_u8",               of_int_wrapped Ast.i32_t Ast.u8_t;
        "of_u16",              of_int_wrapped Ast.i32_t Ast.u16_t;
        "of_u32",              of_int Ast.i32_t Ast.u32_t;
        "of_u64",              of_int Ast.i32_t Ast.u64_t;
        "of_usize",            of_int Ast.i32_t Ast.usize_t;

        "of_i64_wrapped",      of_int_wrapped Ast.i32_t Ast.i64_t;
        "of_isize_wrapped",    of_int_wrapped Ast.i32_t Ast.isize_t;
        "of_u32_wrapped",      of_int_wrapped Ast.i32_t Ast.u32_t;
        "of_u64_wrapped",      of_int_wrapped Ast.i32_t Ast.u64_t;
        "of_usize_wrapped",    of_int_wrapped Ast.i32_t Ast.usize_t;
      ]
    let arg2_funcs = []
    let arg3_funcs = []
  end
  module U32 : PARSLEY_MOD = struct
    let name = "U32"
    let arg0_funcs = []
    let arg1_funcs = [
        "of_byte",             of_byte   Ast.u32_t;
        "of_string",           of_string Ast.u32_t;
        "of_bytes",            of_bytes  Ast.u32_t;
        "of_string_unsafe",    of_string_unsafe Ast.u32_t;
        "of_bytes_unsafe",     of_bytes_unsafe  Ast.u32_t;

        "of_i8",               of_int Ast.u32_t Ast.i8_t;
        "of_i16",              of_int Ast.u32_t Ast.i16_t;
        "of_i32",              of_int Ast.u32_t Ast.i32_t;
        "of_i64",              of_int Ast.u32_t Ast.i64_t;
        "of_isize",            of_int Ast.u32_t Ast.isize_t;
        "of_u8",               of_int_wrapped Ast.u32_t Ast.u8_t;
        "of_u16",              of_int_wrapped Ast.u32_t Ast.u16_t;
        "of_u64",              of_int Ast.u32_t Ast.u64_t;
        "of_usize",            of_int Ast.u32_t Ast.usize_t;

        "of_i8_wrapped",       of_int_wrapped Ast.u32_t Ast.i8_t;
        "of_i16_wrapped",      of_int_wrapped Ast.u32_t Ast.i16_t;
        "of_i32_wrapped",      of_int_wrapped Ast.u32_t Ast.i32_t;
        "of_i64_wrapped",      of_int_wrapped Ast.u32_t Ast.i64_t;
        "of_isize_wrapped",    of_int_wrapped Ast.u32_t Ast.isize_t;
        "of_u64_wrapped",      of_int_wrapped Ast.u32_t Ast.u64_t;
        "of_usize_wrapped",    of_int_wrapped Ast.u32_t Ast.usize_t;
      ]
    let arg2_funcs = []
    let arg3_funcs = []
  end
  module I64 : PARSLEY_MOD = struct
    let name = "I64"
    let arg0_funcs = []
    let arg1_funcs = [
        "of_byte",             of_byte   Ast.i64_t;
        "of_string",           of_string Ast.i64_t;
        "of_bytes",            of_bytes  Ast.i64_t;
        "of_string_unsafe",    of_string_unsafe Ast.i64_t;
        "of_bytes_unsafe",     of_bytes_unsafe  Ast.i64_t;

        "of_i8",               of_int_wrapped Ast.i64_t Ast.i8_t;
        "of_i16",              of_int_wrapped Ast.i64_t Ast.i16_t;
        "of_i32",              of_int_wrapped Ast.i64_t Ast.i32_t;
        "of_isize",            of_int Ast.i64_t Ast.isize_t;
        "of_u8",               of_int_wrapped Ast.i64_t Ast.u8_t;
        "of_u16",              of_int_wrapped Ast.i64_t Ast.u16_t;
        "of_u32",              of_int_wrapped Ast.i64_t Ast.u32_t;
        "of_u64",              of_int Ast.i64_t Ast.u64_t;
        "of_usize",            of_int Ast.i64_t Ast.usize_t;

        "of_isize_wrapped",    of_int_wrapped Ast.i64_t Ast.isize_t;
        "of_u64_wrapped",      of_int_wrapped Ast.i64_t Ast.u64_t;
        "of_usize_wrapped",    of_int_wrapped Ast.i64_t Ast.usize_t;
      ]
    let arg2_funcs = []
    let arg3_funcs = []
  end
  module U64 : PARSLEY_MOD = struct
    let name = "U64"
    let arg0_funcs = []
    let arg1_funcs = [
        "of_byte",             of_byte   Ast.u64_t;
        "of_string",           of_string Ast.u64_t;
        "of_bytes",            of_bytes  Ast.u64_t;
        "of_string_unsafe",    of_string_unsafe Ast.u64_t;
        "of_bytes_unsafe",     of_bytes_unsafe  Ast.u64_t;

        "of_i8",               of_int Ast.u64_t Ast.i8_t;
        "of_i16",              of_int Ast.u64_t Ast.i16_t;
        "of_i32",              of_int Ast.u64_t Ast.i32_t;
        "of_i64",              of_int Ast.u64_t Ast.i64_t;
        "of_isize",            of_int Ast.u64_t Ast.isize_t;
        "of_u8",               of_int_wrapped Ast.u64_t Ast.u8_t;
        "of_u16",              of_int_wrapped Ast.u64_t Ast.u16_t;
        "of_u32",              of_int_wrapped Ast.u64_t Ast.u32_t;

        "of_i8_wrapped",       of_int_wrapped Ast.u64_t Ast.i8_t;
        "of_i16_wrapped",      of_int_wrapped Ast.u64_t Ast.i16_t;
        "of_i32_wrapped",      of_int_wrapped Ast.u64_t Ast.i32_t;
        "of_i64_wrapped",      of_int_wrapped Ast.u64_t Ast.i64_t;
        "of_isize_wrapped",    of_int_wrapped Ast.u64_t Ast.isize_t;
      ]
    let arg2_funcs = []
    let arg3_funcs = []
  end
  module Isize : PARSLEY_MOD = struct
    let name = "Isize"
    let arg0_funcs = []
    let arg1_funcs = [
        "of_byte",           of_byte   Ast.isize_t;
        "of_string",         of_string Ast.isize_t;
        "of_bytes",          of_bytes  Ast.isize_t;
        "of_string_unsafe",  of_string_unsafe Ast.isize_t;
        "of_bytes_unsafe",   of_bytes_unsafe  Ast.isize_t;

        "of_i8",             of_int_wrapped Ast.isize_t Ast.i8_t;
        "of_i16",            of_int_wrapped Ast.isize_t Ast.i16_t;
        "of_i32",            of_int_wrapped Ast.isize_t Ast.i32_t;
        "of_u8",             of_int_wrapped Ast.isize_t Ast.u8_t;
        "of_u16",            of_int_wrapped Ast.isize_t Ast.u16_t;
        "of_u32",            of_int_wrapped Ast.isize_t Ast.u32_t;
        "of_u64",            of_int Ast.isize_t Ast.u64_t;
        "of_usize",          of_int Ast.isize_t Ast.usize_t;
        "of_u64_wrapped",    of_int_wrapped Ast.isize_t Ast.u64_t;
        "of_usize_wrapped",  of_int_wrapped Ast.isize_t Ast.usize_t;
      ]
    let arg2_funcs = []
    let arg3_funcs = []
  end
  module Usize : PARSLEY_MOD = struct
    let name = "Usize"
    let arg0_funcs = []
    let arg1_funcs = [
        "of_byte",           of_byte   Ast.usize_t;
        "of_string",         of_string Ast.usize_t;
        "of_bytes",          of_bytes  Ast.usize_t;
        "of_string_unsafe",  of_string_unsafe Ast.usize_t;
        "of_bytes_unsafe",   of_bytes_unsafe  Ast.usize_t;

        "of_i8",             of_int Ast.usize_t Ast.i8_t;
        "of_i16",            of_int Ast.usize_t Ast.i16_t;
        "of_i32",            of_int Ast.usize_t Ast.i32_t;
        "of_i64",            of_int Ast.usize_t Ast.i64_t;
        "of_u8",             of_int_wrapped Ast.usize_t Ast.u8_t;
        "of_u16",            of_int_wrapped Ast.usize_t Ast.u16_t;
        "of_u32",            of_int_wrapped Ast.usize_t Ast.u32_t;

        "of_i8_wrapped",     of_int_wrapped Ast.usize_t Ast.i8_t;
        "of_i16_wrapped",    of_int_wrapped Ast.usize_t Ast.i16_t;
        "of_i32_wrapped",    of_int_wrapped Ast.usize_t Ast.i32_t;
        "of_i64_wrapped",    of_int_wrapped Ast.usize_t Ast.i64_t;
      ]
    let arg2_funcs = []
    let arg3_funcs = []
  end
end

module PList = struct
  let head lc (v: value) : value =
    match v with
      | V_list [] -> fault lc (Invalid_argument ("List.head", "0-length list"))
      | V_list (h :: _) -> h
      | _ -> internal_error lc (Type_error ("List.head", 1, vtype_of v, T_list T_empty))

  let tail lc (v: value) : value =
    match v with
      | V_list [] -> fault lc (Invalid_argument ("List.tail", "0-length list"))
      | V_list (_ :: tl) -> V_list tl
      | _ -> internal_error lc (Type_error ("List.tail", 1, vtype_of v, T_list T_empty))

  let index lc (l: value) (r: value) : value =
    match l, r with
      | V_list l, V_int (tr, r) when tr = Ast.usize_t ->
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
          internal_error lc (Type_error ("List.index", 2, vtype_of r, T_int Ast.usize_t))
      | _, _ ->
          internal_error lc (Type_error ("List.index", 1, vtype_of l, T_list T_empty))

  let index_unsafe lc (l: value) (r: value) : value =
    match index lc l r with
      | V_option (Some v) ->
          v
      | V_option None ->
          let err = Unsafe_operation_failure("List.index_unsafe") in
          fault lc err
      | _ ->
          assert false

  let length lc (v: value) : value =
    match v with
      | V_list l -> V_int (Ast.usize_t, Int64.of_int (List.length l))
      | _ -> internal_error lc (Type_error ("List.length", 1, vtype_of v, T_list T_empty))

  let cons lc (l: value) (r: value) : value =
    match r with
      | V_list r ->
          V_list (l :: r)
      | _ ->
          internal_error lc (Type_error ("List.cons", 2, vtype_of r, T_list T_empty))

  let concat lc (l: value) (r: value) : value =
    match l, r with
      | V_list l, V_list r ->
          V_list (l @ r)
      | V_list _, _ ->
          internal_error lc (Type_error ("List.concat", 2, vtype_of r, T_list T_empty))
      | _, _ ->
          internal_error lc (Type_error ("List.concat", 1, vtype_of l, T_list T_empty))

  let flatten lc (v: value) : value =
    let exp_t = T_list (T_list T_empty) in
    let err = Type_error ("List.flatten", 1, vtype_of v, exp_t) in
    let conv e = match e with
        | V_list e -> e
        | _ -> internal_error lc err in
    match v with
      | V_list l -> let l' = safe_map conv l in
                    V_list (List.concat l')
      | _ -> internal_error lc err

  let rev lc (v: value) : value =
    match v with
      | V_list l -> V_list (List.rev l)
      | _ -> internal_error lc (Type_error ("List.rev", 1, vtype_of v, T_list T_empty))

  let repl lc (v: value) (i: value) : value =
    match i with
      | V_int (ti, i) when ti = Ast.usize_t && Int64.compare i Int64.zero < 0 ->
          fault lc (Invalid_argument ("List.repl", "count is negative"))
      | V_int (ti, i) when ti = Ast.usize_t ->
          (* TODO: resource bound check on i *)
          let l = List.init (Int64.to_int i) (fun _ -> v) in
          V_list l
      | _ ->
          internal_error lc (Type_error ("List.repl", 2, vtype_of i, T_int Ast.usize_t))

  (* Higher order functions (e.g. `map` and `map2`) are implemented
     via macro-like code-generation. *)

  module List : PARSLEY_MOD = struct
    let name = "List"
    let arg0_funcs = []
    let arg1_funcs = [
        "head",               head;
        "tail",               tail;
        "length",             length;
        "flatten",            flatten;
        "rev",                rev;
      ]
    let arg2_funcs = [
        "cons",               cons;
        "concat",             concat;
        "index",              index;
        "index_unsafe",       index_unsafe;
        "repl",               repl;
      ]
    let arg3_funcs = []
  end

end

module PString = struct
  let empty _lc : value =
    V_string ""

  let concat lc (l: value) (r: value) : value =
    match l, r with
      | V_string l, V_string r ->
          V_string (l ^ r)
      | V_string _, _ ->
          internal_error lc (Type_error ("String.concat", 2, vtype_of r, T_string))
      | _, _ ->
          internal_error lc (Type_error ("String.concat", 1, vtype_of l, T_string))

  let to_bytes lc (v: value) : value =
    match v with
      | V_string s ->
          let len = String.length s in
          let rec mk acc i =
            if i < 0 then acc else mk (V_char s.[i] :: acc) (i - 1) in
          V_list (mk [] (len - 1))
      | _ ->
          internal_error lc (Type_error ("String.to_bytes", 1, vtype_of v, T_string))

  (* no character set support yet, so bytes and characters are currently equivalent *)

  let of_bytes lc (v: value) : value =
    let exp_t = T_list T_byte in
    let err = Type_error ("String.of_bytes", 1, vtype_of v, exp_t) in
    let conv v =
      match v with
        | V_char c -> c
        | _ -> internal_error lc err in
    match v with
      | V_list l ->
          let l = safe_map conv l in
          let buf = Buffer.create 16 in
          List.iter (Buffer.add_char buf) l;
          V_option (Some (V_string (Buffer.contents buf)))
      | _ ->
          internal_error lc err

  let of_bytes_unsafe lc (v: value) : value =
    match of_bytes lc v with
      | V_option None ->
          fault lc (Unsafe_operation_failure "String.of_bytes_unsafe")
      | V_option (Some s) ->
          s
      | _ ->
          assert false

  (* internal helpers *)
  let try_to_string (v: value) : string option =
    match v with
      | V_string s -> Some s
      | V_list vs when List.for_all
                         (function | V_char _ -> true | _ -> false)
                         vs ->
          (* Coerce conversion for a list of bytes. *)
          let b = Buffer.create 64 in
          List.iter (function | V_char c -> Buffer.add_char b c
                              | _ -> assert false) vs;
          Some (Buffer.contents b)
      | _ -> None
  let to_byte_list (s: string) : value =
    V_list (List.of_seq (Seq.map (fun c -> V_char c) (String.to_seq s)))

  let of_literal lc (v: value) : value =
    match try_to_string v with
      | Some s ->
          V_string s
      | None ->
          internal_error lc (Type_error ("String.of_literal", 1, vtype_of v, T_string))

  module String : PARSLEY_MOD = struct
    let name = "String"
    let arg0_funcs = [
        "empty",            empty;
      ]
    let arg1_funcs = [
        "to_bytes",         to_bytes;
        "of_bytes",         of_bytes;
        "of_bytes_unsafe",  of_bytes_unsafe;
        "of_literal",       of_literal;
      ]
    let arg2_funcs = [
        "concat",           concat;
      ]
    let arg3_funcs = []
  end

end

(* assumes big-endian byte order *)
let bits_to_int lc fn (t: Ast.num_t) (bs: bool list) : Int64.t =
  let width = Builtins.get_width t in
  let i, _ =
    List.fold_left (fun (i, cnt) b ->
        if   cnt >= width
        then fault lc (Overflow fn)
        else let i = Int64.shift_left i 1 in
             let b = if b then 1L else 0L in
             Int64.logor i b, cnt + 1
      ) (0L, 0) bs in
  Builtins.wrap_int_bounds t i

let make_big_endian (bs: bool list) : bool list =
  let bytes, bits, _ =
    List.fold_left (fun (bytes, bits, bit_ofs) b ->
        let bits = b :: bits in
        if   bit_ofs = 7
        then let byte = List.rev bits in
             (byte @ bytes), [], 0
        else bytes, bits, bit_ofs + 1
      ) ([], [], 0) bs in
  List.rev bits @ bytes

let bits_by_endian (e: endian) (bs: bool list) : bool list =
  match e with
    | E_big -> bs
    | E_little -> make_big_endian bs

module PBits = struct
  (* TODO: safe version of this conversion *)
  let to_int t lc (v: value) : value =
    let fn = "Bits.to_" ^ Ast.str_of_num_t t in
    match v with
      | V_bitvector [] ->
          fault lc (Invalid_argument (fn, "0-length bitvector"))
      | V_bitvector bs ->
          let i = bits_to_int lc fn t bs in
          V_int (t, i)
      | _ ->
          internal_error lc (Type_error (fn, 1, vtype_of v, T_bitvector))

  let to_int_endian t lc (e: value) (v: value) : value =
    let fn = "Bits.to_" ^ Ast.str_of_num_t t ^ "_endian" in
    let e = match endian_of e with
        | Some e ->
            e
        | None ->
            internal_error lc (Type_error (fn, 1, vtype_of e, T_adt "endian")) in
    match v with
      | V_bitvector [] ->
          fault lc (Invalid_argument (fn, "0-length bitvector"))
      | V_bitvector bs ->
          let bs = bits_by_endian e bs in
          let i = bits_to_int lc fn t bs in
          V_int (t, i)
      | _ ->
          internal_error lc (Type_error (fn, 2, vtype_of v, T_bitvector))

  let to_bool lc (v: value) : value =
    match v with
      | V_bit b -> V_bool b
      | _ -> internal_error lc (Type_error ("Bits.to_bool", 1, vtype_of v, T_bit))

  let of_bool lc (v: value) : value =
    match v with
      | V_bool b -> V_bit b
      | _ -> internal_error lc (Type_error ("Bits.of_bool", 1, vtype_of v, T_bool))

  let to_bit lc (v: value) : value =
    match v with
      | V_bitvector [b] ->
          V_bit b
      | V_bitvector bs  ->
          let m = Printf.sprintf "%d-length bitvector" (List.length bs) in
          fault lc (Invalid_argument ("Bits.to_bit", m))
      | _ ->
          internal_error lc (Type_error ("Bits.to_bit", 1, vtype_of v, T_bitvector))

  let of_bit lc (v: value) : value =
    match v with
      | V_bit b -> V_bitvector [b]
      | _ -> internal_error lc (Type_error ("Bits.of_bit", 1, vtype_of v, T_bit))

  let mk_bv lc op len v =
    (* TODO: resource bound check on len *)
    if   Int64.compare len Int64.zero >= 0
    then V_bitvector (List.init (Int64.to_int len) (fun _ -> v))
    else fault lc (Invalid_argument (op, "negative size"))

  let ones lc (v: value) : value =
    match v with
      | V_int (ti, i) when ti = Ast.usize_t ->
          mk_bv lc "Bits.ones" i true
      | _ ->
          internal_error lc (Type_error ("Bits.ones", 1, vtype_of v, T_int Ast.usize_t))

  let zeros lc (v: value) : value =
    match v with
      | V_int (ti, i) when ti = Ast.usize_t ->
          mk_bv lc "Bits.zeros" i false
      | _ ->
          internal_error lc (Type_error ("Bits.zeros", 1, vtype_of v, T_int Ast.usize_t))

  module Bits : PARSLEY_MOD = struct
    let name = "Bits"
    let arg0_funcs = []
    let arg1_funcs = [
        "to_i8",              to_int Ast.i8_t;
        "to_u8",              to_int Ast.u8_t;
        "to_i16",             to_int Ast.i16_t;
        "to_u16",             to_int Ast.u16_t;
        "to_i32",             to_int Ast.i32_t;
        "to_u32",             to_int Ast.u32_t;
        "to_i64",             to_int Ast.i64_t;
        "to_u64",             to_int Ast.u64_t;
        "to_isize",           to_int Ast.isize_t;
        "to_usize",           to_int Ast.usize_t;

        "to_bool",            to_bool;
        "of_bool",            of_bool;
        "to_bit",             to_bit;
        "of_bit",             of_bit;
        "ones",               ones;
        "zeros",              zeros;
      ]
    let arg2_funcs = [
        "to_i16_endian",      to_int_endian Ast.i16_t;
        "to_u16_endian",      to_int_endian Ast.u16_t;
        "to_i32_endian",      to_int_endian Ast.i32_t;
        "to_u32_endian",      to_int_endian Ast.u32_t;
        "to_i64_endian",      to_int_endian Ast.i64_t;
        "to_u64_endian",      to_int_endian Ast.u64_t;
        "to_isize_endian",    to_int_endian Ast.isize_t;
        "to_usize_endian",    to_int_endian Ast.usize_t;
      ]
    let arg3_funcs = []
  end
end

module VSet = Set.Make(struct type t = value
                              let compare = compare
                       end)
module PSet = struct
  let empty _lc : value =
    V_set []

  let add lc (v: value) (e: value) : value =
    match v with
      | V_set [] ->
          V_set [e]
      | V_set ((se :: _) as vs) ->
          let etyp = vtype_of e in
          let setyp = vtype_of se in
          (* This can be expensive but can be turned off after initial testing *)
          if   List.exists (fun se -> vtype_of se != setyp) vs
          then assert false;
          if   setyp != etyp
          then internal_error lc (Type_error ("Set.add", 2, etyp, setyp));
          let set = VSet.of_list vs in
          V_set (VSet.elements (VSet.add e set))
      | _ ->
          internal_error lc (Type_error ("Set.add", 1, vtype_of v, T_set T_empty))

  let mem lc (v: value) (e: value) : value =
    match v with
      | V_set [] ->
          V_bool false
      | V_set ((se :: _) as vs) ->
          let etyp = vtype_of e in
          let setyp = vtype_of se in
          (* This can be expensive but can be turned off after initial testing *)
          if   List.exists (fun se -> vtype_of se != setyp) vs
          then assert false;
          if   setyp != etyp
          then internal_error lc (Type_error ("Set.mem", 2, etyp, setyp));
          let set = VSet.of_list vs in
          V_bool (VSet.mem e set)
      | _ ->
          internal_error lc (Type_error ("Set.mem", 1, vtype_of v, T_set T_empty))

  module Set : PARSLEY_MOD = struct
    let name = "Set"
    let arg0_funcs = [
        "empty",               empty;
      ]
    let arg1_funcs = []
    let arg2_funcs = [
        "add",                 add;
        "mem",                 mem;
      ]
    let arg3_funcs = []
  end
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
          if   List.exists (fun ke -> vtype_of ke != mktyp) ks
          then assert false;
          if   List.exists (fun ve -> vtype_of ve != mvtyp) vs
          then assert false;
          if   mktyp != ktyp
          then internal_error lc (Type_error ("Map.add", 2, ktyp, mktyp));
          if   mvtyp != vtyp
          then internal_error lc (Type_error ("Map.add", 3, vtyp, mvtyp));
          let map = VMap.of_seq (List.to_seq kvs) in
          let map = VMap.add k v map in
          V_map (List.of_seq (VMap.to_seq map))
      | _ ->
          let exp_t = T_map (vtype_of k, vtype_of v) in
          internal_error lc (Type_error ("Map.add", 1, vtype_of m, exp_t))

  let mem lc (m: value) (k: value) : value =
    match m with
      | V_map [] ->
          V_bool false
      | V_map (((mk, mv) :: _) as kvs) ->
          let mktyp, mvtyp = vtype_of mk, vtype_of mv in
          let ktyp = vtype_of k in
          let ks, vs = List.split kvs in
          (* This can be expensive but can be turned off after initial testing *)
          if   List.exists (fun ke -> vtype_of ke != mktyp) ks
          then assert false;
          if   List.exists (fun ve -> vtype_of ve != mvtyp) vs
          then assert false;
          if   mktyp != ktyp
          then internal_error lc (Type_error ("Map.mem", 2, ktyp, mktyp));
          let map = VMap.of_seq (List.to_seq kvs) in
          V_bool (VMap.mem k map)
      | _ ->
          let exp_t = T_map (vtype_of k, T_empty) in
          internal_error lc (Type_error ("Map.mem", 1, vtype_of m, exp_t))

  let find lc (m: value) (k: value) : value =
    match m with
      | V_map [] ->
          V_option None
      | V_map (((mk, mv) :: _) as kvs) ->
          let mktyp, mvtyp = vtype_of mk, vtype_of mv in
          let ktyp = vtype_of k in
          let ks, vs = List.split kvs in
          (* This can be expensive but can be turned off after initial testing *)
          if   List.exists (fun ke -> vtype_of ke != mktyp) ks
          then assert false;
          if   List.exists (fun ve -> vtype_of ve != mvtyp) vs
          then assert false;
          if   mktyp != ktyp
          then internal_error lc (Type_error ("Map.find", 2, ktyp, mktyp));
          let map = VMap.of_seq (List.to_seq kvs) in
          V_option (VMap.find_opt k map)
      | _ ->
          let exp_t = T_map (vtype_of k, T_empty) in
          internal_error lc (Type_error ("Map.find", 1, vtype_of m, exp_t))

  let find_unsafe lc (m: value) (k: value) : value =
    match find lc m k with
      | V_option None ->
          fault lc (Unsafe_operation_failure "Map.find_unsafe")
      | V_option (Some v) ->
          v
      | _ ->
          assert false

  module Map : PARSLEY_MOD = struct
    let name = "Map"
    let arg0_funcs = [
        "empty",               empty;
      ]
    let arg1_funcs = []
    let arg2_funcs = [
        "mem",                 mem;
        "find",                find;
        "find_unsafe",         find_unsafe;
      ]
    let arg3_funcs = [
        "add",                 add;
      ]
  end
end

(* stdlib modules *)
let stdlib_mods : (module PARSLEY_MOD) list = [
    (module PByte.Byte);
    (module PInt.I8);
    (module PInt.U8);
    (module PInt.I16);
    (module PInt.U16);
    (module PInt.I32);
    (module PInt.U32);
    (module PInt.I64);
    (module PInt.U64);
    (module PInt.Isize);
    (module PInt.Usize);
    (module PList.List);
    (module PString.String);
    (module PBits.Bits);
    (module PSet.Set);
    (module PMap.Map);
  ]

(* top-level operator calls *)

let val_of_lit (l: Ast.primitive_literal) : value =
  match l with
    | Ast.PL_int (i, n)  -> V_int (n, Int64.of_int i)
    | Ast.PL_bytes s     -> PString.to_byte_list s
    | Ast.PL_unit        -> V_unit
    | Ast.PL_bool b      -> V_bool b
    | Ast.PL_bit b       -> V_bit b
    | Ast.PL_bitvector v -> V_bitvector v

let apply_unop (op: Ast.unop) v loc =
  match op with
    | Uminus t -> Builtins.int_uminus t loc v
    | Inot t   -> Builtins.int_not t loc v
    | Not      -> Builtins.bool_not loc v
    | Neg_b    -> Builtins.bitvector_negate loc v

let apply_binop (op: Ast.binop) vl vr loc =
  let bin = match op with
      | Lt t    -> Builtins.less_than t
      | Gt t    -> Builtins.greater_than t
      | Lteq t  -> Builtins.le_than t
      | Gteq t  -> Builtins.ge_than t
      | Eq      -> Builtins.equals
      | Neq     -> Builtins.not_equals
      | Plus t  -> Builtins.int_plus t
      | Minus t -> Builtins.int_minus t
      | Mult t  -> Builtins.int_mul t
      | Mod t   -> Builtins.int_mod t
      | Div t   -> Builtins.int_div t
      | Iand t  -> Builtins.int_and t
      | Ior t   -> Builtins.int_or t
      | Ixor t  -> Builtins.int_xor t
      | Lshft t -> Builtins.int_lshft t
      | Rshft t -> Builtins.int_rshft t
      | Ashft t -> Builtins.int_ashft t
      | Land    -> Builtins.bool_and
      | Lor     -> Builtins.bool_or
      | Or_b    -> Builtins.bv_or
      | And_b   -> Builtins.bv_and
      | Plus_s  -> PString.concat
      | At      -> PList.concat
      | Cons    -> PList.cons
      | Index   -> PList.index in
  bin loc vl vr
