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
open Typing
open Cfg
open Dfa

(* This file constructs DFA transition tables for regular expressions. *)

type regexp_error =
  | Unknown_regexp_nonterm of Ast.ident
  | Negative_seq_bound
  | Nonconstant_seq_bound
  | Cross_module_regexp of Ast.mname * Ast.ident * Ast.mname

exception Error of Location.t * regexp_error

let error_msg = function
  | Unknown_regexp_nonterm id ->
      Printf.sprintf "Unknown regexp nonterminal `%s'." (Location.value id)
  | Negative_seq_bound ->
      "Regexp bounds cannot be negative."
  | Nonconstant_seq_bound ->
      "Non-constant regexp bounds are not supported."
  | Cross_module_regexp (m, id, m') ->
      Printf.sprintf
        "Compilation of external regexp `%s%s' in module `%s' is not supported."
        (AstUtils.mk_modprefix m) (Location.value id) (AstUtils.str_of_mod m')

(* position generator *)
let get_pos_generator () =
  let pos = ref 0 in
  let new_pos () =
    incr pos;
    !pos in
  new_pos

type meta =
  {m_firstpos:  PosSet.t;
   m_lastpos:   PosSet.t;
   m_nullable:  bool}

let firstpos (r: meta re) = r.re_aux.m_firstpos
let lastpos  (r: meta re) = r.re_aux.m_lastpos
let nullable (r: meta re) = r.re_aux.m_nullable

let chars_of_char c pos =
  R_chars (CharSet.singleton c, pos)

(* a string literal is converted into a sequence tree whose root
   ends the literal *)
let lower_literal new_pos (l: Ast.literal) : unit re =
  let mk_re r = {re = r; re_aux = ()} in
  let l = Location.value l in
  let len = String.length l in
  if   len = 0
  then mk_re R_empty
  else let rec inner acc idx =
         if   idx = len then acc
         else let c = chars_of_char l.[idx] (new_pos ()) in
              let re = R_seq (acc, mk_re c) in
              inner (mk_re re) (idx + 1) in
       inner (mk_re (chars_of_char l.[0] (new_pos ()))) 1

(* a char range is converted into a choice tree whose root terminates
   the range *)
let choices_of_char_range new_pos sc ec : unit re_desc =
  (* This should have been checked during type-checking *)
  assert (Char.code sc <= Char.code ec);
  let s, e = Char.code sc, Char.code ec in
  let rec folder acc idx =
    if   idx > e
    then acc
    else folder (CharSet.add (Char.chr idx) acc) (idx + 1) in
  (* the assert above ensures a non-empty set *)
  R_chars (folder CharSet.empty s, new_pos ())

(* a wildcard re is a choice amongst all possible byte values *)
let wildcard_re new_pos =
  let rec loop acc n =
    if   n < 0
    then acc
    else loop (CharSet.add (Char.chr n) acc) (n - 1) in
  R_chars (loop CharSet.empty 255, new_pos ())

(* a re list is converted into an in-order seq *)
let seq_of_list (res: unit re list) : unit re =
  let mk_re r = {re = r; re_aux = ()} in
  let rec folder acc = function
    | [] -> acc
    | n :: rest -> folder (mk_re (R_seq (n, acc))) rest in
  match List.rev res with
    | [] -> mk_re R_empty
    | h :: t -> folder h t

(* when splicing an re into another, or repeating it, we need to re-position it *)
let rec relocate new_pos re =
  let wrap r = {re with re = r} in
  match re.re with
    | R_empty ->
        re
    | R_end _ ->
        wrap (R_end (new_pos ()))
    | R_chars (cs, _) ->
        wrap (R_chars (cs, new_pos ()))
    | R_choice (l, r) ->
        wrap (R_choice (relocate new_pos l, relocate new_pos r))
    | R_seq (l, r) ->
        wrap (R_seq (relocate new_pos l, relocate new_pos r))
    | R_star r' ->
        wrap (R_star (relocate new_pos r'))

(* a re repeated n times *)
let bounded_rep re n new_pos =
  let rec loop acc n =
    if   n = 0
    then acc
    else loop (relocate new_pos re :: acc) (n - 1) in
  seq_of_list (loop [] n)

(* desugar a literal set *)
let re_of_litset (renv: re_env) m' new_pos (ls: Ast.mod_qual Ast.literal_set) : unit re =
  let mk_re r = {re = r; re_aux = ()} in
  match ls.literal_set with
    | LS_type (m, id)
         when m = AstUtils.stdlib && TypeAlgebra.is_character_class id ->
        let cc = Location.value id in
        let chars = List.assoc cc TypeAlgebra.character_classes in
        let chars = CharSet.of_list (Array.to_list chars) in
        mk_re (R_chars (chars, new_pos ()))
    | LS_type (m, id) ->
        (* Cross-module regexp compilation is not supported. *)
        (if   m <> AstUtils.stdlib && not (AstUtils.mod_equiv m m')
         then let err = Cross_module_regexp (m, id, m') in
              raise (Error (ls.literal_set_loc, err)));
        (match StringMap.find_opt (Location.value id) renv with
           | Some (_, re) -> relocate new_pos re
           | None         -> let loc = Location.loc id in
                             raise (Error (loc, Unknown_regexp_nonterm id))
        )
    | LS_set lls ->
        (* a literal set is converted into a choice tree whose root
           terminates the set *)
        (match lls with
           | [] -> mk_re R_empty
           | h :: t -> List.fold_left (fun acc l ->
                           mk_re (R_choice (acc, lower_literal new_pos l))
                         ) (lower_literal new_pos h) t)
    | LS_diff ({literal_set = LS_type (m, cc); _},
               {literal_set = LS_set ls'; _})
         when m = AstUtils.stdlib ->
        let chars =
          List.assoc (Location.value cc) TypeAlgebra.character_classes in
        let chars = CharSet.of_list (Array.to_list chars) in
        let chars = List.fold_left (fun chars cs ->
                        let cs = Location.value cs in
                        (* This should have been converted during
                           type-checking *)
                        assert (String.length cs = 1);
                        CharSet.remove cs.[0] chars
                      ) chars ls' in
        mk_re (if CharSet.is_empty chars
               then R_empty (* TODO: generate a warning or error? *)
               else R_chars (chars, new_pos ()))
    | LS_diff _ ->
        (* This should have been checked during type-checking *)
        assert false
    | LS_range (s, e) ->
        let ss, es = Location.value s, Location.value e in
        assert (String.length ss = String.length es);
        let rs =
          Seq.fold_left (fun acc (idx, sc) ->
              let ec = es.[idx] in
              mk_re (choices_of_char_range new_pos sc ec) :: acc
            ) [] (String.to_seqi ss) in
        seq_of_list rs

(* desugar a top-level regexp *)
let rec simplify (renv: re_env) new_pos (r: regexp) : unit re =
  let mk_re r = {re = r; re_aux = ()} in
  match r.regexp with
    | RX_empty ->
        mk_re R_empty
    | RX_literals ls ->
        let m' = AstUtils.infer_mod r.regexp_mod in
        re_of_litset renv m' new_pos ls
    | RX_wildcard ->
        mk_re (wildcard_re new_pos)
    | RX_type (m, id) ->
        (* Cross-module regexp compilation is not supported. *)
        let m' = AstUtils.infer_mod r.regexp_mod in
        (if   m <> AstUtils.stdlib && not (AstUtils.mod_equiv m m')
         then let err = Cross_module_regexp (m, id, m') in
              raise (Error (r.regexp_loc, err)));
        (match StringMap.find_opt (Location.value id) renv with
           | Some (_, re) -> relocate new_pos re
           | None         -> let loc = Location.loc id in
                             raise (Error (loc, Unknown_regexp_nonterm id)))
    | RX_star (r', None) ->
        mk_re (R_star (simplify renv new_pos r'))
    | RX_star (r', Some e) ->
        (match (TypedAstUtils.const_fold e).expr with
           | E_literal (PL_int (i, _)) when i < 0 ->
               (* FIXME: we should really assert here, now that `i` is
                  required to be `usize`. *)
               raise (Error (e.expr_loc, Negative_seq_bound))
           | E_literal (PL_int (i, _)) ->
               bounded_rep (simplify renv new_pos r') i new_pos
           | _ ->
               raise (Error (e.expr_loc, Nonconstant_seq_bound)))
    | RX_opt r' ->
        mk_re (R_choice (simplify renv new_pos r', mk_re R_empty))
    | RX_choice rs ->
        (* reverse list to preserve ordering after fold *)
        (match List.rev rs with
           | [] ->
               mk_re R_empty
           | r' :: rs' ->
               List.fold_left (fun acc r' ->
                   mk_re (R_choice (simplify renv new_pos r', acc))
                 ) (simplify renv new_pos r') rs')
    | RX_seq rs ->
        (* reverse list to preserve ordering after fold *)
        (match List.rev rs with
           | [] ->
               mk_re R_empty
           | r' :: rs' ->
               List.fold_left (fun acc r' ->
                   mk_re (R_seq (simplify renv new_pos r', acc))
                 ) (simplify renv new_pos r') rs')

(* the bottom-up analysis constructs an annotated version of the re *)
let rec analyse (re: unit re) : meta re =
  let mk_re r m = {re = r; re_aux = m} in
  match re.re with
    | R_end p ->
        let ps = PosSet.singleton p in
        let m = {m_firstpos = ps;
                 m_lastpos  = ps;
                 m_nullable = false} in
        mk_re (R_end p) m
    | R_empty ->
        let m = {m_firstpos = PosSet.empty;
                 m_lastpos  = PosSet.empty;
                 m_nullable = true} in
        mk_re R_empty m
    | R_chars (c, p) ->
        (* We should be using R_empty for empty charsets *)
        assert (not (CharSet.is_empty c));
        let ps = PosSet.singleton p in
        let m = {m_firstpos = ps;
                 m_lastpos  = ps;
                 m_nullable = false} in
        mk_re (R_chars (c, p)) m
    | R_choice (l, r) ->
        let l', r' = analyse l, analyse r in
        let m = {m_firstpos = PosSet.union (firstpos l') (firstpos r');
                 m_lastpos  = PosSet.union (lastpos l') (lastpos r');
                 m_nullable = nullable l' || nullable r'} in
        mk_re (R_choice (l', r')) m
    | R_seq (l, r) ->
        let l', r' = analyse l, analyse r in
        let m = {m_firstpos = if   nullable l'
                              then PosSet.union (firstpos l') (firstpos r')
                              else firstpos l';
                 m_lastpos  = if   nullable r'
                              then PosSet.union (lastpos l') (lastpos r')
                              else lastpos r';
                 m_nullable = nullable l' && nullable r'} in
        mk_re (R_seq (l', r')) m
    | R_star r ->
        let r' = analyse r in
        let m = {m_firstpos = firstpos r';
                 m_lastpos  = lastpos r';
                 m_nullable = true} in
        mk_re (R_star r') m

(* compute followpos as a map from a position to its follow-set. *)
let mk_follows (r: meta re) : PosSet.t PosMap.t =
  let add_fols m p ps =
    let init = match PosMap.find_opt p m with
        | None -> PosSet.empty
        | Some s -> s in
    PosMap.add p (PosSet.union init ps) m in
  let fold acc lps fps =
    PosSet.fold (fun p acc ->
        add_fols acc p fps
      ) lps acc in
  let rec fol acc r =
    match r.re with
      | R_end _ | R_empty | R_chars _ -> acc
      | R_choice (l', r') ->
          fol (fol acc l') r'
      | R_seq (l', r') ->
          let acc = fol (fol acc l') r' in
          fold acc (lastpos l') (firstpos r')
      | R_star r' ->
          fold (fol acc r') (lastpos r') (firstpos r') in
  fol PosMap.empty r

(* construct a map from positions to the chars at that position *)
let mk_pos_map r : CharSet.t PosMap.t =
  let rec recurse acc r =
    match r.re with
      | R_empty | R_end _ ->
          acc
      | R_chars (cs, p) ->
          assert (not (PosMap.mem p acc));
          PosMap.add p cs acc
      | R_choice (l, r) | R_seq (l, r) ->
          recurse (recurse acc l) r
      | R_star r ->
          recurse acc r in
  recurse PosMap.empty r

(* exported simplifier api *)

let build_re (renv: re_env) (re: regexp) : unit re =
  let new_pos = get_pos_generator () in
  simplify renv new_pos re

(* the core DFA building algorithm. *)

let build_dfa (trace: bool) (renv: re_env) (re: regexp) : dfa =
  let mk_re r = {re = r; re_aux = ()} in
  let new_pos = get_pos_generator () in
  (* desugar *)
  let r = simplify renv new_pos re in
  if   trace
  then (Printf.printf "Simplifying regexp from:\n%!";
        AstPrinter.print_regexp_flush TypeInfer.typed_auxp re;
        Printf.printf "\n  to:\n%!";
        Cfg_printer.print_re () r);
  (* construct end-marked version, noting the end-position *)
  let end_pos = new_pos () in
  let rend = mk_re (R_end end_pos) in
  let r = mk_re (R_seq (r, rend)) in
  (* analyse and compute the position map *)
  let rm = analyse r in
  let follows = mk_follows rm in
  let pos_map = mk_pos_map rm in  (* chars at each position *)
  let start = firstpos rm in      (* starting state *)
  let pending = StateSet.singleton start in   (* pending states *)
  let marked = StateSet.empty in  (* finished (or marked) states *)
  let rec loop_states table pending marked =
    match StateSet.choose_opt pending with
      | None ->
          marked, table
      | Some st ->
          let pending = StateSet.remove st pending in
          let marked = StateSet.add st marked in
          let rec loop_chars table pending i =
            if   i = -1
            then table, pending
            else let c = Char.chr i in
                 (* find positions that can be transitioned to on c *)
                 let next =
                   PosSet.fold (fun p next ->
                       (* check if we can transition from p on c *)
                       match PosMap.find_opt p pos_map with
                         | None ->
                             (* this could only happen at the end position *)
                             assert (p = end_pos);
                             next
                         | Some cs ->
                             if   CharSet.mem c cs
                             then (* c transitions to any position in follows(p) *)
                                  (match PosMap.find_opt p follows with
                                     | None ->
                                         (* no transitions at all from p *)
                                         next
                                     | Some ps ->
                                         PosSet.union next ps)
                             else next
                     ) st PosSet.empty in
                 if   PosSet.is_empty next
                 then loop_chars table pending (i - 1)
                 else let pending =
                        (* update pending if next is a new state *)
                        if   StateSet.mem next marked || StateSet.mem next pending
                        then pending
                        else StateSet.add next pending in
                      let table = TTable.add (st, c) next table in
                      loop_chars table pending (i - 1) in
          (* loop over ascii charset *)
          let table, pending = loop_chars table pending 255 in
          loop_states table pending marked in
  let states, table = loop_states TTable.empty pending marked in
  (* find accepting states *)
  let accept = StateSet.fold (fun st accept ->
                   if   PosSet.mem end_pos st
                   then StateSet.add st accept
                   else accept
                 ) states StateSet.empty in
  let dfa = {dfa_states      = states;
             dfa_start       = start;
             dfa_accepts     = accept;
             dfa_transitions = table;
             dfa_loc         = re.regexp_loc;
             dfa_regex = r} in
  if   trace
  then (Printf.printf "\nBuilt DFA:%!";
        Cfg_printer.print_dfa dfa);
  dfa

let re_of_character_class cc : unit re =
  let new_pos = get_pos_generator () in
  {re = R_chars ((CharSet.of_list (Array.to_list cc)), new_pos ());
   re_aux = ()}
