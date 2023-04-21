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

(* Zipper data structure for the ANF IR. *)

open Parsing
open Typing
open Anf_common
open Anfscf
open Anf
open Interpreter_common
open Values

(* Pair ANF atoms with their values *)
type anf_val = av * value

(* There are two root contexts, one for expressions, and the other for
   a statement block.  Since a statement contains expressions, an
   expression context could be nested inside a statement context.  *)

(* This zipper marks pre-computation locations, as needed for a
   context hole or continuation. *)
type bfi_info = modul * Ast.ident * TypingEnvironment.bitfield_info
type sinfo = Site.site option
type zexp =
  | Zexp_root of aexp (* the whole expression *)
  | Zexp_apply of fv * anf_val list * av list * Location.t * sinfo * zexp
  | Zexp_unop of Ast.unop * Location.t * sinfo * zexp
  | Zexp_binop1 of Ast.binop * av * av * Location.t * sinfo * zexp
  | Zexp_binop2 of Ast.binop * anf_val * av * Location.t * sinfo * zexp
  | Zexp_bits_of_rec of bfi_info * Location.t * sinfo * zexp
  | Zexp_rec_of_bits of bfi_info * Location.t * sinfo * zexp
  | Zexp_bitrange of int * int * Location.t * sinfo * zexp
  | Zexp_match of (modul * string * string) * Location.t * sinfo * zexp
  | Zexp_field of Ast.ident * Location.t * sinfo * zexp
  | Zexp_cases of av * (apat * aexp) list * sinfo * zexp
  | Zexp_let of var * aexp * sinfo * zexp
  | Zexp_cast of Ast.type_expr * Location.t * sinfo * zexp
  | Zexp_print of bool * av * Location.t * sinfo * zexp
  | Zexp_letpat of occurrence * var * aexp * sinfo * zexp
  (* This is used to mark end of scopes for introduced variables.
     The `sinfo` is inherited from the introducing context. *)
  | Zexp_drop_var of var * sinfo * zexp

and zstmt =
  | Zstmt_root of astmt (* the whole statement *)
  | Zstmt_set_var of var * Location.t * sinfo * zstmt
  | Zstmt_set_field of var * Ast.ident list * Location.t * sinfo * zstmt
  | Zstmt_print of bool * av * sinfo * zstmt
  | Zstmt_let of var * astmt * sinfo * zstmt
  | Zstmt_cases of av * (apat * astmt) list * sinfo * zstmt
  | Zstmt_block of astmt list * sinfo * zstmt
  | Zstmt_letpat of occurrence * var * astmt * sinfo * zstmt
  | Zstmt_stmt of astmt * zstmt

  (* This is used to mark end of scopes for introduced variables.
     The `sinfo` is inherited from the introducing context. *)
  | Zstmt_drop_var of var * sinfo * zstmt

(*

let zexp_sinfo : zexp -> sinfo = function
  | Zexp_apply (_, _, _, _, si, _)
  | Zexp_unop (_, _, si, _)
  | Zexp_binop1 (_, _, _, _, si, _)
  | Zexp_binop2 (_, _, _, _, si, _)
  | Zexp_bits_of_rec (_, _, si, _)
  | Zexp_rec_of_bits (_, _, si, _)
  | Zexp_bitrange (_,_, _, si, _)
  | Zexp_match (_, _, si, _)
  | Zexp_field (_, _, si, _)
  | Zexp_cases (_, _, si, _)
  | Zexp_let (_, _, si, _)
  | Zexp_cast (_, _, si, _)
  | Zexp_print (_, _, _, si, _)
  | Zexp_letpat (_, _, _, si, _)
    -> si
  | Zexp_root _
    -> None

let zstmt_sinfo : zstmt -> sinfo = function
  | Zstmt_set_var (_, _, si, _)
  | Zstmt_set_field (_, _, _, si, _)
  | Zstmt_print (_, _, si, _)
  | Zstmt_let (_, _, si, _)
  | Zstmt_cases (_, _, si, _)
  | Zstmt_block (_, si, _)
  | Zstmt_letpat (_, _, _, si, _)
    -> si
  | Zstmt_stmt (s, _)
    -> s.astmt_site
  | Zstmt_root _
    -> None

 *)
