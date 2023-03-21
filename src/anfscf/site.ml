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
open Anf_common

(* Sites annotate computation events of interest to execution
   monitors, such as bindings to variables and changes to control
   flow.  They specify which (source-level) variables are in scope at
   the site, and the corresponding IR variables. *)

(* Site identifiers and their generation. *)

type site_id  = int

type site_id_gen = unit -> site_id

let mk_id_gen () : site_id_gen =
  let sid = ref 0 in
  fun () -> let id = !sid in
            incr sid;
            id

let str_of_site_id (s: site_id) =
  string_of_int s

(* Sites for grammar events of interest to execution monitors. *)
type site_type =
  | ST_let      (* value assignment to source variable *)
  | ST_apply    (* function application                *)
  | ST_case     (* pattern variable assignment         *)
  | ST_fun      (* function entry                      *)
  | SS_regex    (* regex dfa execution                 *)
  | SS_cond     (* conditional: constraint, if         *)
  | SS_view     (* view operations                     *)
  | SS_bitmode  (* bitmode entry and exit              *)
  | SS_choice   (* choice-related events               *)
  | SS_break    (* loop exits                          *)
  | SS_call     (* calls to non-terminal matching      *)
  | SS_dynamic  (* dynamic assertions                  *)

(* Source-level free variables in scope at a site and their
   corresponding IR variables. *)
type site_var_type =
  | SV_fun
  | SV_val
type site_var =
  {sv_ident: Ast.ident;
   sv_type:  site_var_type;
   sv_var:   Anf_common.varid}

type site =
  {site_id:   site_id;
   site_type: site_type;
   site_vars: site_var StringMap.t;
   site_loc:  Location.t}

module SiteMap = Map.Make(Int)
module SiteSet = Set.Make(Int)
