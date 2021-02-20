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

type label = int

let _counter = ref 0

let fresh_label () : label =
  incr _counter;
  (!_counter :> label)

let to_string (l: label) : string =
  Printf.sprintf "%d" (l :> int)

module LabelSet = struct
  module S = Set.Make (struct
                 type t = label
                 let compare = compare
               end)
  include S
end

module LabelMap = struct
  module M = Map.Make (struct
                 type t = label
                 let compare = compare
               end)
  include M
end
