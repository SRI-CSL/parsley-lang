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
open Anf
open Anf_pattern

(* expression normalizer *)

type subexp =
  | S_var of av
  | S_let of var * aexp * av

let make_var v t l =
  {v;
   v_typ = t;
   v_loc = l}

let make_av v t l =
  {av     = v;
   av_typ = t;
   av_loc = l}

(* When normalizing subexpressions, avoid creating let bindings
   for subexpressions that are already variables, since that will
   result in inefficient redundant renaming. *)
let rec subnorm tenv venv (e: exp) : subexp * VEnv.t =
  match e.expr with
    | E_var v ->
        let v' = VEnv.lookup venv v in
        let v' = make_av (AV_var v') e.expr_aux e.expr_loc in
        S_var v', venv
    | _ ->
        let e', venv  = normalize_exp tenv venv e in
        let vid, venv = VEnv.gen venv in
        let v  = make_var vid e.expr_aux e.expr_loc in
        let av = make_av (AV_var vid) e.expr_aux e.expr_loc in
        S_let (v, e', av), venv

(* The main expression normalizer *)
and normalize_exp tenv venv (e: exp) : aexp * VEnv.t =
  let loc = e.expr_loc in
  let wrap e' =
    {aexp     = e';
     aexp_typ = e.expr_aux;
     aexp_loc = loc} in
  let make_lets binds ae =
    (* The bindings in [binds] are executed in reverse order,
       relying on the fact that the [binds] are themselves in
       reverse order having been generated by a List.fold_left. *)
    List.fold_left (fun ae' (v, ae) ->
        {aexp     = AE_let (v, ae, ae');
         aexp_typ = ae.aexp_typ;
         aexp_loc = ae.aexp_loc}
      ) ae binds in
  match e.expr with
    | E_var v ->
        let v' = VEnv.lookup venv v in
        let t  = e.expr_aux in
        let l  = Location.loc v in
        let v' = make_av (AV_var v') t l in
        wrap (AE_val v'), venv
    | E_literal l ->
        let v' = make_av (AV_lit l) e.expr_aux e.expr_loc in
        wrap (AE_val v'), venv
    | E_constr (c, es) ->
        (* Order of evaluation is left-to-right *)
        let (binds, vs), venv =
          List.fold_left (fun ((binds, vs), venv) e ->
              let se, venv = subnorm tenv venv e in
              (match se with
                 | S_var av          -> binds, av :: vs
                 | S_let (v, ae, av) -> (v, ae) :: binds, av :: vs
              ), venv
            ) (([], []), venv) es in
        let v  = AV_constr (c, List.rev vs) in
        let av = make_av v e.expr_aux e.expr_loc in
        let ae = make_lets binds (wrap (AE_val av)) in
        ae, venv
    | E_record fs ->
        (* Order of evaluation is first to last *)
        let (binds, fvs), venv =
          List.fold_left (fun ((binds, vs), venv) (f, e) ->
              let se, venv = subnorm tenv venv e in
              (match se with
                 | S_var av          -> binds, (f, av) :: vs
                 | S_let (v, ae, av) -> (v, ae) :: binds, (f, av) :: vs
              ), venv
            ) (([], []), venv) fs in
        let v  = AV_record (List.rev fvs) in
        let av = make_av v e.expr_aux e.expr_loc in
        let ae = make_lets binds (wrap (AE_val av)) in
        ae, venv
    | E_apply (f, es) ->
        (* Order of evaluation is function first, and then args
           left-to-right. *)
        let sf, venv  = subnorm tenv venv f in
        let binds, fv = match sf with
            | S_var av          -> [], av
            | S_let (v, ae, av) -> [v, ae], av in
        let (binds, vs), venv =
          List.fold_left (fun ((binds, vs), venv) e ->
              let se, venv = subnorm tenv venv e in
              (match se with
                 | S_var av          -> binds, av :: vs
                 | S_let (v, ae, av) -> (v, ae) :: binds, av :: vs
              ), venv
            ) ((binds, []), venv) es in
        let ae = wrap (AE_apply (fv, List.rev vs)) in
        let ae = make_lets binds ae in
        ae, venv
    | E_unop (op, e) ->
        let se, venv  = subnorm tenv venv e in
        let binds, av = match se with
            | S_var av          -> [], av
            | S_let (v, ae, av) -> [v, ae], av in
        let ae = wrap (AE_unop (op, av)) in
        let ae = make_lets binds ae in
        ae, venv
    | E_binop (op, l, r) ->
        (* Order of evaluation is left then right *)
        (* TODO: boolean short-circuit *)
        let sl, venv  = subnorm tenv venv l in
        let sr, venv  = subnorm tenv venv r in
        let binds, lv = match sl with
            | S_var av          -> [], av
            | S_let (v, ae, av) -> [v, ae], av in
        let binds, rv = match sr with
            | S_var av          -> binds, av
            | S_let (v, ae, av) -> (v, ae) :: binds, av in
        let ae = wrap (AE_binop (op, lv, rv)) in
        let ae = make_lets binds ae in
        ae, venv
    | E_recop (r, op, e) ->
        let se, venv  = subnorm tenv venv e in
        let binds, av = match se with
            | S_var av          -> [], av
            | S_let (v, ae, av) -> [v, ae], av in
        let ae = wrap (AE_recop (r, op, av)) in
        let ae = make_lets binds ae in
        ae, venv
    | E_bitrange (e, f, l) ->
        let se, venv  = subnorm tenv venv e in
        let binds, av = match se with
            | S_var av          -> [], av
            | S_let (v, ae, av) -> [v, ae], av in
        let ae = wrap (AE_bitrange (av, f, l)) in
        let ae = make_lets binds ae in
        ae, venv
    | E_match (e, c) ->
        let se, venv  = subnorm tenv venv e in
        let binds, av = match se with
            | S_var av          -> [], av
            | S_let (v, ae, av) -> [v, ae], av in
        let ae = wrap (AE_match (av, c)) in
        let ae = make_lets binds ae in
        ae, venv
    | E_field (e, f) ->
        let se, venv  = subnorm tenv venv e in
        let binds, av = match se with
            | S_var av          -> [], av
            | S_let (v, ae, av) -> [v, ae], av in
        let ae = wrap (AE_field (av, f)) in
        let ae = make_lets binds ae in
        ae, venv
    | E_mod_member (m, id) ->
        wrap (AE_mod_member (m, id)), venv
    | E_cast (e, t) ->
        let se, venv  = subnorm tenv venv e in
        let binds, av = match se with
            | S_var av          -> [], av
            | S_let (v, ae, av) -> [v, ae], av in
        let ae = wrap (AE_cast (av, t)) in
        let ae = make_lets binds ae in
        ae, venv
    | E_let (p, pe, e) ->
        let spe, venv = subnorm tenv venv pe in
        let binds, av = match spe with
            | S_var av          -> [], av
            | S_let (v, ae, av) -> [v, ae], av in
        (* this is a special case of pattern matching *)
        let cases = [p, e] in
        let ae, venv = normalize_exp_case tenv venv av cases loc in
        let ae = make_lets binds ae in
        ae, venv
    | E_case (e, cases) ->
        let se, venv  = subnorm tenv venv e in
        let binds, av = match se with
            | S_var av          -> [], av
            | S_let (v, ae, av) -> [v, ae], av in
        let ae, venv = normalize_exp_case tenv venv av cases loc in
        let ae = make_lets binds ae in
        ae, venv

and normalize_exp_case (tenv: TypingEnvironment.environment)
      (venv: VEnv.t) (scrutinee: av) (cases: (pat * exp) list) loc
    : aexp * VEnv.t =
  (* Construct the pattern-action matrix, and collect the action-label
     to action map as well as the pattern variables bound in each
     action. *)
  let pmat, act_infos, _ =
    List.fold_left (fun (pmat, act_infos, albl) (p, e) ->
        ([p], albl) :: pmat,
        (albl, (e, pvar_paths p)) :: act_infos,
        albl + 1
      ) ([], [], 0) cases in
  (* construct a decision tree for the pattern-action matrix *)
  let dt = to_decision_tree tenv pmat in
  (* convert a decision tree into an ANF expression *)
  let rec unfold venv dt : aexp * VEnv.t =
    match dt with
      | Leaf a ->
          (* TODO: if any action is invoked more than once, create a
             function for the action and call it at the leafs for it.
             Otherwise, the action can be inlined at the single leaf
             resolving to it. *)
          let act, pvs = List.assoc a act_infos in
          (* Bind a new ANF variable in the variable environment for
             each pvar *)
          let letpats, venv =
            List.fold_left (fun (letpats, venv) (v, t, occ) ->
                if VEnv.is_bound venv v
                then letpats, venv
                else let avar, venv = VEnv.bind venv v in
                     let var = make_var avar t (Location.loc v) in
                     (var, occ) :: letpats, venv

              ) ([], venv) pvs in
          (* Normalize the action expression in this augmented
             variable environment *)
          let ae, venv = normalize_exp tenv venv act in
          (* Wrap the normalized action in the letpat bindings to
             bind the new ANF variables *)
          let ae =
            List.fold_left (fun ae (avar, occ) ->
                {aexp     = AE_letpat (avar, (scrutinee, occ), ae);
                 aexp_typ = ae.aexp_typ;
                 aexp_loc = ae.aexp_loc}
              ) ae letpats in
          ae, venv
      | Switch (occ, subtree) ->
          (* Convert the subtree into cases for an ANF case.  The type
             of the sub-term being matched at the occurence is that of
             any of the head constructors.  The result type of the ANF
             case will be that of any of the nested case actions. *)
          let cases, venv, opt_typ =
            List.fold_left (fun (cases, venv, _) (con, occ_typ, loc, dt) ->
                let aexp, venv = unfold venv dt in
                let apat =
                  {apat = (match con with
                             | Con (c, _) -> AP_variant c
                             | Lit l      -> AP_literal l
                             | Default    -> AP_wildcard);
                   apat_typ = occ_typ;
                   apat_loc = loc} in
                (apat, aexp) :: cases, venv, Some (occ_typ, aexp.aexp_typ)
              ) ([], venv, None) subtree in
          (* There should be at least one case (e.g. the default) *)
          let occ_typ, case_typ = match opt_typ with
              | None          -> assert false
              | Some (ot, ct) -> ot, ct in
          (* Bind an ANF variable to the subterm being scrutinized,
             unless it is the root of a variable term *)
          (match scrutinee.av with
             | AV_var v when occ = root_occurrence ->
                 let var =
                   make_var v scrutinee.av_typ scrutinee.av_loc in
                 {aexp     = AE_case (var, cases);
                  aexp_typ = case_typ;
                  aexp_loc = loc},
                 venv
             | _ ->
                 let v, venv = VEnv.gen venv in
                 let var  = make_var v occ_typ Location.ghost_loc in
                 let aexp =
                   {aexp     = AE_case (var, cases);
                    aexp_typ = case_typ;
                    aexp_loc = loc} in
                 (* Wrap the case in a letpat for the ANF variable *)
                 {aexp     = AE_letpat (var, (scrutinee, occ), aexp);
                  aexp_typ = aexp.aexp_typ;
                  aexp_loc = loc},
                 venv) in
  (* construct the anf *)
  unfold venv dt

let normalize_fun tenv venv (f: func) : afun * VEnv.t =
  let fident, venv = VEnv.bind venv f.fun_defn_ident in
  let params, venv =
    (* fold_right ensures params are in the correct order in the
       struct, but causes them to be bound in reverse order in the
       VEnv. *)
    List.fold_right (fun (v, _) (ps, venv) ->
        let p, venv = VEnv.bind venv v in
        p :: ps, venv
      ) f.fun_defn_params ([], venv) in
  let body, venv = normalize_exp tenv venv f.fun_defn_body in
  {afun_ident     = fident;
   afun_params    = params;
   afun_body      = body;
   afun_recursive = f.fun_defn_recursive;
   afun_loc       = f.fun_defn_loc },
  venv

let rec normalize_stmt tenv venv (s: stmt) : astmt * VEnv.t =
  let loc = s.stmt_loc in
  let wrap s' =
    {astmt     = s';
     astmt_loc = loc} in
  let rec make_lets binds sn =
    (* The bindings in [binds] are executed in reverse order,
       relying on the fact that the [binds] are themselves in
       reverse order having been generated by a List.fold_left. *)
    match binds with
      | [] ->
          sn
      | (v, ae) :: rest ->
          make_lets rest {astmt     = AS_let (v, ae, sn);
                          astmt_loc = s.stmt_loc} in
  match s.stmt with
    | S_assign (l, r) ->
        let ln, venv = normalize_exp tenv venv l in
        let rn, venv = normalize_exp tenv venv r in
        (* the left hand side should be a variable or a record field *)
        let sn =
          match ln.aexp with
            | AE_val {av = AV_var v; _} ->
                let v = make_var v ln.aexp_typ ln.aexp_loc in
                AS_set_var (v, rn)
            | AE_field ({av = AV_var v; _}, f) ->
                let v = make_var v ln.aexp_typ ln.aexp_loc in
                AS_set_field (v, f, rn)
            | _ ->
                raise (Error (Unassignable_expression ln.aexp_loc)) in
        wrap sn, venv
    | S_let (p, e, ss) ->
        (* handle this similar to E_let *)
        let se, venv  = subnorm tenv venv e in
        let binds, av = match se with
            | S_var av          -> [], av
            | S_let (v, ae, av) -> [v, ae], av in
        let cases = [p, ss] in
        let sn, venv = normalize_stmt_case tenv venv av cases loc in
        let sn = make_lets binds sn in
        sn, venv
    | S_case (e, cases) ->
        let se, venv = subnorm tenv venv e in
        let binds, av = match se with
            | S_var av          -> [], av
            | S_let (v, ae, av) -> [v, ae], av in
        let sn, venv = normalize_stmt_case tenv venv av cases loc in
        let sn = make_lets binds sn in
        sn, venv

and normalize_stmt_case (tenv: TypingEnvironment.environment)
      (venv: VEnv.t) (scrutinee: av) (cases: (pat * stmt list) list) loc
    : astmt * VEnv.t =
  (* The structure of this function essentially follows that of
     normalize_exp_case above. *)
  let pmat, act_infos, _ =
    List.fold_left (fun (pmat, act_infos, albl) (p, e) ->
        ([p], albl) :: pmat,
        (albl, (e, pvar_paths p)) :: act_infos,
        albl + 1
      ) ([], [], 0) cases in
  let dt = to_decision_tree tenv pmat in
  let rec unfold venv dt : astmt * VEnv.t =
    match dt with
      | Leaf a ->
          (* TODO: if any action is invoked more than once, create a
             function for the action and call it at the leafs for it.
             Otherwise, the action can be inlined at the single leaf
             resolving to it. *)
          let act, pvs = List.assoc a act_infos in
          (* Bind a new ANF variable in the variable environment for
             each pvar *)
          let letpats, venv =
            List.fold_left (fun (letpats, venv) (v, t, occ) ->
                if VEnv.is_bound venv v
                then letpats, venv
                else let avar, venv = VEnv.bind venv v in
                     let var = make_var avar t (Location.loc v) in
                     (var, occ) :: letpats, venv
              ) ([], venv) pvs in
          (* Normalize the action block in this augmented
             variable environment (note the order reversal) *)
          let act, venv =
            List.fold_left (fun (astmts, venv) s ->
                let astmt, venv = normalize_stmt tenv venv s in
                astmt :: astmts, venv
              ) ([], venv) act in
          (* Wrap the normalized action in the letpat bindings to
             bind the new ANF variables, and reorder the reversed
             block. *)
          let astmt =
            {astmt     = AS_block (List.rev act);
             astmt_loc = Location.ghost_loc} in
          let astmt =
            List.fold_left (fun astmt (avar, occ) ->
                {astmt     = AS_letpat (avar, (scrutinee, occ), astmt);
                 astmt_loc = Location.ghost_loc}
              ) astmt letpats in
          astmt, venv
      | Switch (occ, subtree) ->
          (* Convert the subtree into cases for an ANF case.  The type
             of the sub-term being matched at the occurence is that of
             any of the head constructors.  The result type of the ANF
             case will be that of any of the nested case actions. *)
          let cases, venv, opt_typ =
            List.fold_left (fun (cases, venv, _) (con, occ_typ, loc, dt) ->
                let astmt, venv = unfold venv dt in
                let apat =
                  {apat = (match con with
                             | Con (c, _) -> AP_variant c
                             | Lit l      -> AP_literal l
                             | Default    -> AP_wildcard);
                   apat_typ = occ_typ;
                   apat_loc = loc} in
                (apat, astmt) :: cases, venv, Some occ_typ
              ) ([], venv, None) subtree in
          (* There should be at least one case (e.g. the default) *)
          let occ_typ = match opt_typ with
              | None    -> assert false
              | Some ot -> ot in
          (* Bind an ANF variable to the subterm being scrutinized,
             unless it is the root of a variable term *)
          (match scrutinee.av with
             | AV_var v when occ = root_occurrence ->
                 let var =
                   make_var v scrutinee.av_typ scrutinee.av_loc in
                 {astmt     = AS_case (var, cases);
                  astmt_loc = loc},
                 venv
             | _ ->
                 let v, venv = VEnv.gen venv in
                 let var  = make_var v occ_typ Location.ghost_loc in
                 let astmt =
                   {astmt     = AS_case (var, cases);
                    astmt_loc = loc} in
                 (* Wrap the case in a letpat for the ANF variable *)
                 {astmt     = AS_letpat (var, (scrutinee, occ), astmt);
                  astmt_loc = loc},
                 venv) in
  unfold venv dt
