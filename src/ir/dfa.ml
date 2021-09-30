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

(* The desugared representation of regexps and their compiled DFAs *)

(* positions of non-empty leaves in the AST of an re *)
type   pos    = Int.t
module PosSet = Set.Make(Int)
module PosMap = Map.Make(Int)

module CharSet = Set.Make(Char)

type 'a re_desc =
  | R_empty
  (* internally used marker to denote the end of an re *)
  | R_end of pos
  (* use a single leaf for a choice between possibly multiple chars *)
  | R_chars of CharSet.t * pos  (* the only leaf with a position *)
  | R_choice of 'a re * 'a re
  | R_seq of 'a re * 'a re
  | R_star of 'a re

and 'a re =
  {re: 'a re_desc;
   re_aux: 'a}

(* This environment maps the definition of a regexp non-terminal to
   its defining location and its desugared re.

   Regular expressions can refer to non-terminals that define other
   regular expressions.  For compilation of the referer re, the
   desugared re for the referee needs to be included into the re of
   the referer.  The compilation context includes the re_env below for
   this purpose.
 *)
module StringMap = Map.Make(String)
type re_env = (Location.t * unit re) StringMap.t

(* The DFA *)

(* TODO: make the state abstract, and speed interpretation by using
   integer identifiers for states. *)

type state = PosSet.t

module StateSet = Set.Make(struct
                      type t = state
                      let compare = compare
                    end)

module TTable = Map.Make(struct
                    type t = state * Char.t
                    let compare = compare
                  end)

type dfa =
  StateSet.t         (* all states *)
  * state            (* starting state *)
  * StateSet.t       (* accepting states *)
  * state TTable.t   (* transition table *)

(* The DFAs for regexp non-terminals *)
type dfa_env = (Location.t * unit re) StringMap.t
