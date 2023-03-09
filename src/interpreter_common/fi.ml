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

(* Function interface: Stdlib and FFI signatures. *)

open Parsing
open Values

type arg0 = Location.t -> value
type arg1 = Location.t -> value -> value
type arg2 = Location.t -> value -> value -> value
type arg3 = Location.t -> value -> value -> value -> value

(* module interface *)

module type PARSLEY_MOD = sig
  val name: string

  val arg0_funcs: (string * arg0) list
  val arg1_funcs: (string * arg1) list
  val arg2_funcs: (string * arg2) list
  val arg3_funcs: (string * arg3) list
end
