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
open Misc
open Ast
open TypingEnvironment

(** Adapted from the algorithm in
    'Warnings for pattern matching', by Luc Maranget.
    Journal of Functional Programming, Volume 17, Issue 3, May 2007. *)

let repeat p n =
  let rec iter n acc =
    if n = 0 then acc
    else iter (n - 1) (p :: acc) in
  iter n []

let arity tenv typ constr =
  let arity, _, _ =
    let dcid =
      AstUtils.canonicalize_dcon
        (Location.value typ) (Location.value constr) in
    lookup_datacon tenv (Location.loc typ) (DName dcid) in
  arity

(** [default_mat m] computes the default matrix for a given pattern
   matrix [m]. *)
let default_mat m =
  let default_row ps =
    match ps with
      | p :: rest  ->
          (match p.pattern with
             | P_wildcard  | P_var _     -> Some rest
             | P_literal _ | P_variant _ -> None)
      | [] -> assert false in
  List.fold_right (fun (p, a) acc ->
      match default_row p with
        | None   -> acc
        | Some r -> (r, a) :: acc
    ) m []

(** [specialize_row_constr tenv (typ, constr) ps] computes the
   specialized version of a pattern row [ps] with respect to the
   constructor [constr] of type [typ]. *)
let specialize_row_constr tenv (typ, constr) ps =
  let arity = arity tenv typ constr in
  match ps with
    | p :: rest ->
        (match p.pattern with
           | P_wildcard
           | P_var _ ->
               let p' = { p with pattern = P_wildcard } in
               Some ((repeat p' arity) @ rest)
           | P_variant ((typ', constr'), ps)
                when Location.value typ' = Location.value typ ->
               if Location.value constr' = Location.value constr
               then (
                 assert (List.length ps = arity);
                 Some (ps @ rest)
               )
               else None
           | P_literal _ ->
               (* Type-check should forbid this. *)
               assert false
           | P_variant ((typ', _), _) ->
               (* Type-check should forbid this assertion failing. *)
               assert (Location.value typ' == Location.value typ);
               None)
    | [] ->
        assert false

(** [specialize_row_literal lit ps] computes the specialized version
    of a pattern row [ps] with respect to the constructor
    corresponding to the literal [lit]. *)
let specialize_row_literal lit ps =
  match ps with
    | p :: rest ->
        (match p.pattern with
           | P_wildcard
           | P_var _ ->
               Some rest
           | P_literal l when l = lit ->
               Some rest
           | P_literal _ ->
               None
           | P_variant _ ->
               (* Type-check should forbid this. *)
               ignore (assert false);
               None)
    | [] ->
        assert false

let specialize_mat tenv mat p =
  let filter mat =
    List.fold_right (fun r acc ->
        match r with
          | None, _   -> acc
          | Some r, a -> (r, a) :: acc
      ) mat [] in
  match p.pattern with
    | P_wildcard | P_var _ ->
        (* these are not constructors *)
        assert false
    | P_literal l ->
        filter (List.map (fun (p, a) ->
                    specialize_row_literal l p, a
                  ) mat)
    | P_variant ((typ, constr), _) ->
        filter (List.map (fun (p, a) ->
                    specialize_row_constr tenv (typ, constr) p, a
                    ) mat)

(** [unused_constructors tenv typ cs] computes the set of unused
    constructors of type [typ] given a list [cs] of used
    constructors. *)
let unused_constructors tenv typ cs =
  let tn = Location.value typ in
  let adti =
    match lookup_adt tenv (TName tn) with
      | None -> assert false
      | Some i -> i in
  let dcons = match adti.adt with
      | Variant dcons -> dcons
      | Record _ -> assert false in
  let dcons =
    List.fold_left (fun acc (DName c, _) ->
        StringSet.add c acc
      ) StringSet.empty dcons in
  List.fold_left (fun acc c ->
      StringSet.remove (Location.value c) acc
    ) dcons cs

(** [check_variant_completeness tenv typ cs] checks whether the list
    [cs] of constructors of type [typ] contains all the constructors
    of the type. *)
let check_variant_completeness tenv typ cs =
  StringSet.is_empty (unused_constructors tenv typ cs)

(* helpers for bitvector patterns *)

let bv_to_int bv =
  List.fold_left (fun i b ->
      let i = Int64.shift_left i 1 in
      Int64.add i (if b then Int64.one else Int64.zero)
    ) Int64.zero bv

let int_to_bv int width =
  let bit_to_bool i =
    Int64.logand i Int64.one == Int64.one in
  let rec iter acc cnt =
    if cnt = width
    then acc
    else let int = Int64.shift_right int cnt in
         let bit = bit_to_bool int in
         iter (bit :: acc) (cnt + 1) in
  iter [] 0

module BVSet = Set.Make(Int64)

let check_bitvector_completeness set width =
  assert (width <= 64);
  let max = Int64.shift_left Int64.one width in
  let rec check i =
    if Int64.equal i max
    then true
    else if BVSet.mem i set
    then check (Int64.succ i)
    else false in
  check Int64.zero

(** [is_complete_sig tenv roots] checks whether the root constructors
    [roots] form a complete signature for their type. *)
let is_complete_sig tenv roots =
  match roots with
    | [] ->
        false
    | p :: rest ->
        (match p.pattern with
           | P_wildcard | P_var _ ->
               (* these are not roots *)
               assert false
           | P_literal PL_unit ->
               List.iter (fun p ->
                   assert (p.pattern = P_literal PL_unit)
                 ) rest;
               true
           | P_literal (PL_string _) ->
               List.iter (fun p ->
                   match p.pattern with
                     | P_literal (PL_string _) -> ()
                     | _ -> assert false
                 ) rest;
               false
           | P_literal (PL_int _) ->
               List.iter (fun p ->
                   match p.pattern with
                     | P_literal (PL_int _) -> ()
                     | _ -> assert false
                 ) rest;
               false
           | P_literal (PL_bool b) ->
               List.fold_left (fun acc p ->
                   match p.pattern with
                     | P_literal (PL_bool b') ->
                         b != b' || acc
                     | _ -> assert false
                 ) false rest
           | P_literal (PL_bit b) ->
               List.fold_left (fun acc p ->
                   match p.pattern with
                     | P_literal (PL_bit b') ->
                         b != b' || acc
                     | _ -> assert false
                 ) false rest
           | P_literal (PL_bitvector bv) ->
               let bvs =
                 List.fold_left (fun acc p ->
                     match p.pattern with
                       | P_literal (PL_bitvector bv') ->
                           assert (List.length bv' == List.length bv);
                           BVSet.add (bv_to_int bv') acc
                       | _ -> assert false
                   )
                   (BVSet.add (bv_to_int bv) BVSet.empty)
                   rest in
               check_bitvector_completeness bvs (List.length bv)
           | P_variant ((t, c), _) ->
               let cs =
                 List.fold_left (fun acc p ->
                     match p.pattern with
                       | P_variant ((t', c'), _) ->
                           assert (Location.value t = Location.value t');
                           c' :: acc
                       | _ ->
                           assert false
                   ) [c] rest in
               check_variant_completeness tenv t cs
        )

(* extract the first column of a pattern matrix *)
let first_col mat =
  List.fold_right (fun row acc ->
      match row with
        | [], _     -> assert false  (* not called for base case *)
        | h :: _, _ -> h :: acc
    ) mat []

(* extract the n'th column of a pattern matrix *)
let nth_col mat n =
  (match mat with
     | [] ->
         assert false
     | (p, _) :: rest ->
         let cols = List.length p in
         assert (0 <= n && n < cols);
         List.iter (fun (p, _) -> assert (cols = List.length p)) rest
  );
  List.map (fun (p, _) -> List.nth p n) mat

(* swap two columns of the matrix *)
let swap_cols m i j =
  let swap row cols =
    assert (List.length row = cols);
    assert (0 <= i && i < cols);
    assert (0 <= j && j < cols);
    let a = Array.of_list row in
    let t = a.(i) in
    a.(i) <- a.(j);
    a.(j) <- t;
    Array.to_list a in
  match m with
    | [] ->
        assert false
    | ((p, _) :: _) as rows ->
        let cols = List.length p in
        let m =
          List.fold_left (fun acc (p, a) ->
              let p' = swap p cols in
              (p', a) :: acc
            ) [] rows in
        List.rev m

(* extract the constructors from a pattern column *)
let roots tenv col =
  (* ensure each constructor appears only once *)
  let rec is_mem ((pat, _) as p) acc =
    match pat.pattern, acc with
      | _, [] ->
          false
      | P_literal l, ({pattern = P_literal l';
                       _}, _) :: _
           when l = l' ->
          true
      | P_variant ((t, c), _), ({pattern = P_variant ((t', c'), _);
                                 _}, _) :: _
           when    Location.value t = Location.value t'
                && Location.value c = Location.value c' ->
          true
      | _, _ :: tl ->
          is_mem p tl in
  let add p acc =
    if   is_mem p acc
    then acc
    else p :: acc in
  List.fold_right (fun p acc ->
      match p.pattern with
        | P_wildcard | P_var _ ->
            (* these are not constructors *)
            acc
        | P_literal _ ->
            (* literals have arity 0 *)
            add (p, 0) acc
        | P_variant ((typ, constr), _) ->
            add (p, arity tenv typ constr) acc
    ) col []
