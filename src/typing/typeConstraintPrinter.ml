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

(*  Adapted from:                                                         *)
(*  Mini, a type inference engine based on constraint solving.            *)
(*  Copyright (C) 2006. François Pottier, Yann Régis-Gianas               *)
(*  and Didier Rémy.                                                      *)

(** This module implements a pretty printer for constraints. *)

open Misc
open PrettyPrinter
open TypeEnvPrinter
open TypeConstraint
open MultiEquation
open Format

(** The constraint over equality between terms. *)
type formula =
  (MultiEquation.crterm, MultiEquation.variable) TypeConstraint.type_constraint

let print_crterm t =
  print_term false t

let print_variable v =
  let vt = print_variable false v in
  if (UnionFind.find v).structure <> None then
    Printf.sprintf "(%s)" vt
  else
    vt

let active_mode mode =
  match mode with
    | Formatter r ->
        Format.set_tags true;
        let formatter = Format.get_formatter_out_functions () in
        Format.set_formatter_out_functions
          {formatter with
           out_string  = r.out;
           out_flush   = r.flush;
           out_newline = r.newline;
           out_spaces  = r.spaces};
        if r.with_tags then (
          set_formatter_stag_functions
            {mark_open_stag   = (fun t -> r.open_tag t; "");
             mark_close_stag  = (fun t -> r.close_tag t; "");
             print_open_stag  = ignore;
             print_close_stag = ignore};
          set_margin r.margin)

    | Txt out ->
          let _ = Format.set_margin 80 in
          let formatter = Format.get_formatter_out_functions () in
          Format.set_formatter_out_functions
            {formatter with
              out_string  = (fun s b e -> output_string out (String.sub s b e));
              out_flush   = (fun () -> flush out);
              out_newline = (fun () -> output_string out "\n");
              out_spaces  = (fun n -> for _ = 0 to n do output_string out " " done)}

let is_let = function
  | CLet _ -> true
  | _      -> false

let paren f =
  print_string "(";
  f ();
  print_string ")"

let printf_constraint mode c =
  let exists = "exists "
  and forall = "forall "
  and andsym = "and" in

  let rec pconstraint c =
    (match c with
       | CTrue _
       | CConjunction [] ->
           print_string "true"

       | CDump _ ->
           print_string "dump"

       | CEquation (_, t1, t2) ->
           printf "%s = %s"
             (print_crterm t1)
             (print_crterm t2)

       | CConjunction (c :: []) ->
           pconstraint c

       | CConjunction (c :: cs) ->
           printf "(";
           pconstraint c;
           List.iter (fun c ->
               printf "@ %s@ " andsym;
               if is_let c then
                 paren (fun () -> pconstraint c)
               else
                 pconstraint c
             ) cs;
           printf ")"

       | CLet ([ Scheme (_, [], fqs, c, h) ], CTrue _)
            when StringMap.empty = h ->
           let rec chop_exists acu = function
             | CLet ([ Scheme (_, [], fqs', c', _) ], CTrue _) ->
                 chop_exists (acu @ fqs') c'
             | lc -> (acu, lc) in
           let (fqs, c) = chop_exists fqs c in
           if (List.length fqs <> 0) then
             print_string exists;
           print_string (print_separated_list " " print_variable fqs);
           if (List.length fqs <> 0) then
             printf ".@,";
           printf "@[<b 2>";
           pconstraint c;
           printf "@]"

       | CLet (schemes, c) ->
           printf "let @[<b>";
           printf_schemes schemes;
           printf "@]@ in@ @[<b>";
           pconstraint c;
           printf "@]"

       | CInstance (_, SName name, t) ->
           printf "%s < %s" name (print_crterm t)
    )

  and printf_schemes  = function
    | [] -> ()
    | [ x ] -> printf_scheme x
    | x :: q -> (printf_scheme x; print_cut (); print_string " ; ";
                 print_cut (); printf_schemes q)

  and is_true = function CTrue _ -> true | _ -> false

  and printf_scheme (Scheme (_, rqs, fqs, c, header)) =
    let len = StringMap.fold (fun _x _k acu -> acu + 1) header 0 in
    printf "";
    if (List.length rqs + List.length fqs <> 0) then
      print_string forall;
    print_string (print_separated_list " " print_variable fqs);
    if rqs <> [] then
      printf " {%s}" (print_separated_list " " print_variable rqs);
    if not (is_true c) then (
      printf "@,[@[<b>";
      pconstraint c;
      printf "@]]");
    if (len <> 0) then print_string " (";
    let f = ref true in
    let sep () = if !f then (f := false; "") else "; " in
    StringMap.iter (fun name (t, _pos) ->
        printf "%s%s : %s"
          (sep ())  name (print_crterm t)
      ) header;
    if (len <> 0) then print_string ")"

  in
  (
    active_mode mode;
    open_box 0;
    pconstraint c;
    close_box ();
    print_newline ();
  )

let print_width_predicate = function
  | WP_less    i -> Printf.sprintf "< %d"  i
  | WP_more    i -> Printf.sprintf "> %d"  i
  | WP_equal   i -> Printf.sprintf "= %d"  i
  | WP_less_eq i -> Printf.sprintf "<= %d" i
  | WP_more_eq i -> Printf.sprintf ">= %d" i

let print_width_constraint wc =
  let rec print = function
    | WC_true ->
        "true"
    | WC_pred (_, v, p) ->
        Printf.sprintf "(%s) %s" (print_variable v) (print_width_predicate p)
    | WC_conjunction cl ->
        let sl = List.map print cl in
        String.concat " && " sl in
  Printf.printf "Width constraints: %s\n" (print wc)
