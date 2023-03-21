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

open Parsing

type varid = string * int  (* globally unique identifiers *)

let string_of_var (v, id) =
  if   v <> "" && id = 1
  then v
  else Printf.sprintf "%s#%d" v id

type modul =
  | M_name   of string
  | M_stdlib

type constr = modul * string * string

(* simplified module qualifiers *)

let modul_of_mname m =
  match m with
    | Ast.(Modul Mod_stdlib)       -> M_stdlib
    | Ast.(Modul (Mod_explicit m)) -> M_name (Location.value m)
    | Ast.(Modul (Mod_inferred m)) -> M_name m

let str_of_modul m =
  match m with
    | M_stdlib -> ""
    | M_name m -> m

let mod_prefix m s =
  match m with
    | M_stdlib -> s
    | M_name m -> Printf.sprintf "%s.%s" m s

let str_of_qname (m, s) =
  mod_prefix m s

let convert_con (m, t, c) =
  (modul_of_mname m), Location.value t, Location.value c

let string_of_constr ((m, t, c): constr) : string =
  mod_prefix m (AstUtils.canonicalize_dcon t c)

(* An occurrence identifies the subterm of the value being scrutinized
   by a pattern.  The list starts from the root and goes towards
   the sub-term.  An empty list indicates the entire value.  Constructor
   arguments are numbered starting from 1. *)

type occurrence = int list
let root_occurrence = []

let string_of_occurrence occ =
  if   occ = []
  then ""
  else "@" ^ (String.concat "/" (List.map string_of_int occ))

(* other useful defs *)

module StringMap = Map.Make(String)
