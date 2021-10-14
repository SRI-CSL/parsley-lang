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
open Ast
open TypingExceptions

module StringSet = Set.Make(String)

(* processing of format decorators *)

type deco_value = ident * deco_arg list

(* Check decorator usage satisfies the following:
   . any decorator should have a single use
   . any decorator key should appear only once
 *)
let check_format_decorator =
  let check_keys a args =
    List.fold_left (fun s kv ->
        match kv with
          | Deco_key k | Deco_keyvalue (k, _) ->
              let ks = Location.value k in
              if StringSet.mem ks s
              then raise (Error (RepeatedDecoratorKey (a, k)))
              else StringSet.add ks s
          ) StringSet.empty args in
  let check_deco s a =
    let at = a.deco_type in
    let ats = Location.value at in
    if StringSet.mem ats s
    then raise (Error (RepeatedDecoratorType at))
    else (ignore (check_keys a.deco_value a.deco_args);
          StringSet.add ats s) in
  function
  | None ->
      ()
  | Some decos ->
      ignore (List.fold_left check_deco StringSet.empty decos)

(* Find the value of a specified decorator type *)
let lookup_decorator_value (name: string) (odecos: decorator list option)
    : deco_value option =
  match odecos with
    | None ->
        None
    | Some ats ->
        let nas = List.filter_map
                    (fun a ->
                      let atn = Location.value a.deco_type in
                      if name = atn
                      then Some (a.deco_value, a.deco_args)
                      else None
                    ) ats in
        (* We checked for uniqueness above *)
        assert (List.length nas = 1);
        Some (List.hd nas)

(* Convert a decorator value into a non-terminal instance, using
   the following rules:

   . the name of the decorator value needs to be upper-case, as for
     non-terminals

   . every decorator key should specify a value, as required for
     inherited attributes of non-terminals

   . each value should either be boolean ('true'/'false').  This
     restriction does not affect current use-cases, but may be relaxed
     if needed.

     The rationale for this restriction is that it allows
     us to enumerate all the ways the non-terminal can be
     instantiated.  For example, if the non-terminal is a regexp
     non-terminal with multiple possible rules (e.g. whitespace), we
     could constant-fold to compute the regexp corresponding to each
     call of this non-terminal.
 *)

(* Perform the conversion described above, and return an untyped
   non-term node. *)
let non_term_of_decorator_value (deco: deco_value)
    : (unit, unit) non_term_instance =
  let mk_bool s loc =
    let bool = Location.mk_loc_val "bool" loc in
    let v = E_constr ((bool, Location.mk_loc_val s loc), []) in
    AstUtils.make_expr_loc v loc in
  let n, args = deco in
  if not (AstUtils.is_valid_nonterm_name (Location.value n))
  then raise (Error (InvalidDecoratorName n));
  let iattrs =
    match args with
      | [] ->
          None
      | _::_ ->
          let ia =
            List.fold_left (fun acc a ->
                match a with
                  | Deco_key k ->
                      let err = UnvaluedDecoratorKey (n, k) in
                      raise (Error err)
                  | Deco_keyvalue (k, v) ->
                      let vs = Location.value v in
                      let loc = Location.loc v in
                      let av = match vs with
                          | "true" ->
                              k, mk_bool "True" loc
                          | "false" ->
                              k, mk_bool "False" loc
                          | _ ->
                              let err =
                                InvalidDecoratorKeyValue (n, k, v) in
                              raise (Error err) in
                      av :: acc
              ) [] args in
          Some (List.rev ia) in
  n, iattrs
