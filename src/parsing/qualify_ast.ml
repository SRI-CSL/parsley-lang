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

(* Conversion of pre-AST to AST. *)

open Ast

module StringSet = Set.Make(String)

type builtins =
  {bltin_type:    string -> bool;
   bltin_field:   string -> bool;
   bltin_value:   string -> bool;
   bltin_nonterm: string -> bool}

type context =
  {ctx_types:    StringSet.t;
   ctx_fields:   StringSet.t;
   ctx_locals:   StringSet.t;
   ctx_nonterms: StringSet.t;
   ctx_bltins:   builtins}

let init_ctx bltins : context =
  {ctx_types    = StringSet.empty;
   ctx_fields   = StringSet.empty;
   ctx_locals   = StringSet.empty;
   ctx_nonterms = StringSet.empty;
   ctx_bltins   = bltins}

let stdlib = AstUtils.stdlib

let mod_name (Modul m) : string =
  match m with
    | Mod_explicit m -> Location.value m
    | Mod_inferred m -> m
    | Mod_stdlib     -> assert false

(* A type identifier is converted as follows:
   - if it is fully qualified, there is no change
   - if it has been locally registered, it is inferred to belong to
     the local module and qualified accordingly, as per lexical
     scoping.
   - if it is a standard library type, it is qualified accordingly.
   - otherwise, it is again inferred to belong to the local module.
 *)

let mod_of_type ctx lm t =
  let tn = Location.value t in
  if      StringSet.mem tn ctx.ctx_types
  then    lm
  else if ctx.ctx_bltins.bltin_type tn
  then    stdlib
  else    lm

let mod_of_nonterm ctx lm id =
  (* The module resolution follows the same precedence as for type
     identifiers. *)
  let n = Location.value id in
  if      StringSet.mem n ctx.ctx_nonterms
  then    lm
  else if ctx.ctx_bltins.bltin_nonterm n
  then    stdlib
  else    lm

let mod_of_field ctx lm f =
  let fn = Location.value f in
  if      StringSet.mem fn ctx.ctx_fields
  then    lm
  else if ctx.ctx_bltins.bltin_field fn
  then    stdlib
  else    lm

let convert_type_expr ctx lm (te: raw_mod gen_type_expr)
    : type_expr =
  let wrap t = {type_expr     = t;
                type_expr_loc = te.type_expr_loc} in
  (* always put bitvector indices in stdlib using `std_qual` flag *)
  let rec conv std_qual te =
    match te.type_expr with
      | TE_tvar t ->
          wrap (TE_tvar t)
      | TE_tname (Modul (Some m), t) ->
          let m = Modul (Mod_explicit m) in
          wrap (TE_tname (m, t))
      | TE_tname (Modul None, t) when std_qual ->
          wrap (TE_tname (stdlib, t))
      | TE_tname (Modul None, t) ->
          let m = mod_of_type ctx lm t in
          wrap (TE_tname (m, t))
      | TE_tapp (({type_expr = TE_tname (Modul None, t); _} as tc), targs)
           when Location.value t = "bitvector" ->
          let tc = conv true tc in
          let targs = List.map (conv true) targs in
          wrap (TE_tapp (tc, targs))
      | TE_tapp (tc, targs) ->
          let tc = conv std_qual tc in
          let targs = List.map (conv std_qual) targs in
          wrap (TE_tapp (tc, targs)) in
  conv false te

let convert_type_decl ctx (td: raw_mod type_decl)
    : mod_qual type_decl =
  let lm = AstUtils.infer_mod td.type_decl_mod in
  let bd = td.type_decl_body in
  let wrap tr =
    {type_rep = tr; type_rep_loc = bd.type_rep_loc} in
  let bd = match bd.type_rep with
    | TR_variant args ->
        let args =
          List.map (function
              | v, None    -> v, None
              | v, Some te -> v, Some (convert_type_expr ctx lm te)
            ) args in
        wrap (TR_variant args)
    | TR_record flds ->
        let flds =
          List.map (fun (f, te) -> f, convert_type_expr ctx lm te)
            flds in
        wrap (TR_record flds)
    | TR_bitfield flds ->
        wrap (TR_bitfield flds)
    | TR_defn te ->
        wrap (TR_defn (convert_type_expr ctx lm te)) in
  {type_decl_ident = td.type_decl_ident;
   type_decl_kind  = td.type_decl_kind;
   type_decl_tvars = td.type_decl_tvars;
   type_decl_body  = bd;
   type_decl_mod   = td.type_decl_mod;
   type_decl_loc   = td.type_decl_loc}

let convert_types ctx (ts: raw_mod type_decl list)
    : context * mod_qual type_decl list =
  (* The types may be mutually recursive, so first register their
     identifiers. *)
  let ctx =
    List.fold_left (fun ctx td ->
        let tn    = Location.value td.type_decl_ident in
        let types = StringSet.add tn ctx.ctx_types in
        let fields = match td.type_decl_body.type_rep with
            | TR_record fs ->
                List.fold_left (fun acc (f, _) ->
                    StringSet.add (Location.value f) acc
                  ) ctx.ctx_fields fs
            | _ ->
                ctx.ctx_fields in
        {ctx with ctx_types  = types;
                  ctx_fields = fields}
      ) ctx ts in
  ctx, List.map (convert_type_decl ctx) ts

let rec convert_pat ctx lm p =
  let wrap p' = {pattern     = p';
                 pattern_loc = p.pattern_loc;
                 pattern_aux = p.pattern_aux} in
  match p.pattern with
    | P_wildcard ->
        ctx, wrap P_wildcard
    | P_var v ->
        (* update local bindings *)
        let vn   = var_name v in
        let locs = StringSet.add vn ctx.ctx_locals in
        let ctx  = {ctx with ctx_locals = locs} in
        ctx, wrap (P_var v)
    | P_literal l ->
        ctx, wrap (P_literal l)
    | P_variant ((Modul (Some m), t, c), args) ->
        let ctx, args =
          List.fold_left (fun (ctx, acc) a ->
              let ctx, a = convert_pat ctx lm a in
              ctx, a :: acc
            ) (ctx, []) args in
        let m = Modul (Mod_explicit m) in
        ctx, wrap (P_variant ((m, t, c), List.rev args))
    | P_variant ((Modul None, t, c), args) ->
        let ctx, args =
          List.fold_left (fun (ctx, acc) a ->
              let ctx, a = convert_pat ctx lm a in
              ctx, a :: acc
            ) (ctx, []) args in
        let m = mod_of_type ctx lm t in
        ctx, wrap (P_variant ((m, t, c), List.rev args))

let rec convert_exp ctx lm e =
  let wrap e' = {expr     = e';
                 expr_loc = e.expr_loc;
                 expr_aux = e.expr_aux} in
  match e.expr with
    | E_var v ->
        (* If this is bound locally, then leave it intact, otherwise
           qualify it with the local module. *)
        let vn = var_name v in
        if   StringSet.mem vn ctx.ctx_locals
        then wrap (E_var v)
        else let loc = Location.loc v in
             let m   = Location.mk_loc_val (mod_name lm) loc in
             let v   = Location.mk_loc_val (var_name v)  loc in
             wrap (E_mod_member (m, v))
    | E_constr ((Modul (Some m), t, c), es) ->
        let es = List.map (convert_exp ctx lm) es in
        let m = Modul (Mod_explicit m) in
        wrap (E_constr ((m, t, c), es))
    | E_constr ((Modul None, t, c), es) ->
        let es = List.map (convert_exp ctx lm) es in
        (* If this is a local type, then qualify it with the local
         * module, else assume it must be in the stdlib. *)
        let tn = Location.value t in
        let m = if   StringSet.mem tn ctx.ctx_types
                then lm
                else stdlib in
        wrap (E_constr ((m, t, c), es))
    | E_record flds ->
        let flds =
          List.map (fun ((m, f), e) ->
              (let m = match m with
                 | Modul (Some m) -> Modul (Mod_explicit m)
                 | Modul None     -> mod_of_field ctx lm f in
               m, f),
              convert_exp ctx lm e) flds in
        wrap (E_record flds)
    | E_apply (f, args) ->
        let f    = convert_exp ctx lm f in
        let args = List.map (convert_exp ctx lm) args in
        wrap (E_apply (f, args))
    | E_unop (op, e) ->
        wrap (E_unop (op, convert_exp ctx lm e))
    | E_binop (op, l, r) ->
        let l = convert_exp ctx lm l in
        let r = convert_exp ctx lm r in
        wrap (E_binop (op, l, r))
    | E_recop ((Modul (Some m), r, op), e) ->
        let e = convert_exp ctx lm e in
        let m = Modul (Mod_explicit m) in
        wrap (E_recop ((m, r, op), e))
    | E_recop ((Modul None, r, op), e) ->
        let e = convert_exp ctx lm e in
        let m = mod_of_type ctx lm r in
        wrap (E_recop ((m, r, op), e))
    | E_bitrange (e, l, r) ->
        let e = convert_exp ctx lm e in
        wrap (E_bitrange (e, l, r))
    | E_match (e, (Modul (Some m), t, c)) ->
        let e = convert_exp ctx lm e in
        let m = Modul (Mod_explicit m) in
        wrap (E_match (e, (m, t, c)))
    | E_match (e, (Modul None, t, c)) ->
        let e = convert_exp ctx lm e in
        let m = mod_of_type ctx lm t in
        wrap (E_match (e, (m, t, c)))
    | E_literal l ->
        wrap (E_literal l)
    | E_field (e, (Modul (Some m), f)) ->
        let e = convert_exp ctx lm e in
        wrap (E_field (e, (Modul (Mod_explicit m), f)))
    | E_field (e, (Modul None, f)) ->
        let e = convert_exp ctx lm e in
        let m = mod_of_field ctx lm f in
        wrap (E_field (e, (m, f)))
    | E_mod_member (m, c) ->
        wrap (E_mod_member (m, c))
    | E_case (e, cls) ->
        let e = convert_exp ctx lm e in
        let cls = List.map (fun (p, e) ->
                      let ctx, p = convert_pat ctx lm p in
                      let e = convert_exp ctx lm e in
                      (p, e)
                    ) cls in
        wrap (E_case (e, cls))
    | E_let (p, e, bd) ->
        let e = convert_exp ctx lm e in
        let ctx, p = convert_pat ctx lm p in
        let bd = convert_exp ctx lm bd in
        wrap (E_let (p, e, bd))
    | E_cast (e, t) ->
        let e = convert_exp ctx lm e in
        let t = convert_type_expr ctx lm t in
        wrap (E_cast (e, t))

let rec convert_stmt ctx lm s =
  let wrap s' = {stmt = s'; stmt_loc = s.stmt_loc} in
  match s.stmt with
    | S_assign (l, r) ->
        let l = convert_exp ctx lm l in
        let r = convert_exp ctx lm r in
        wrap (S_assign (l, r))
    | S_let (p, e, bd) ->
        let e = convert_exp ctx lm e in
        let ctx, p = convert_pat ctx lm p in
        let bd = List.map (convert_stmt ctx lm) bd in
        wrap (S_let (p, e, bd))
    | S_case (e, cls) ->
        let e = convert_exp ctx lm e in
        let cls = List.map (fun (p, ss) ->
                      let ctx, p = convert_pat ctx lm p in
                      let ss = List.map (convert_stmt ctx lm) ss in
                      (p, ss)
                    ) cls in
        wrap (S_case (e, cls))
    | S_print e ->
        wrap (S_print (convert_exp ctx lm e))

let convert_act ctx lm a =
  let ss, e = a.action_stmts in
  let ss = List.map (convert_stmt ctx lm) ss in
  let e = match e with
      | None   -> None
      | Some e -> Some (convert_exp ctx lm e) in
  {action_stmts = ss, e; action_loc = a.action_loc}

let rec convert_literals ctx lm l =
  let wrap l' = {literal_set     = l';
                 literal_set_loc = l.literal_set_loc} in
  match l.literal_set with
    | LS_type (Modul (Some m), id) ->
        let m = Modul (Mod_explicit m) in
        wrap (LS_type (m, id))
    | LS_type (Modul None, id) ->
        let m = mod_of_nonterm ctx lm id in
        wrap (LS_type (m, id))
    | LS_set ls ->
        wrap (LS_set ls)
    | LS_diff (l, r) ->
        let l = convert_literals ctx lm l in
        let r = convert_literals ctx lm r in
        wrap (LS_diff (l, r))
    | LS_range (s, e) ->
        wrap (LS_range (s, e))

let rec convert_regexp ctx r =
  let lm = AstUtils.infer_mod r.regexp_mod in
  let wrap r' = {regexp     = r';
                 regexp_loc = r.regexp_loc;
                 regexp_mod = r.regexp_mod;
                 regexp_aux = r.regexp_aux} in
  match r.regexp with
    | RX_empty ->
        wrap RX_empty
    | RX_wildcard ->
        wrap RX_wildcard
    | RX_literals ls ->
        wrap (RX_literals (convert_literals ctx lm ls))
    | RX_type (Modul (Some m), id) ->
        let m = Modul (Mod_explicit m) in
        wrap (RX_type (m, id))
    | RX_type (Modul None, id) ->
        let m = mod_of_nonterm ctx lm id in
        wrap (RX_type (m, id))
    | RX_star (r, None) ->
        let r = convert_regexp ctx r in
        wrap (RX_star (r, None))
    | RX_star (r, Some e) ->
        let e = convert_exp ctx lm e in
        let r = convert_regexp ctx r in
        wrap (RX_star (r, Some e))
    | RX_opt r ->
        wrap (RX_opt (convert_regexp ctx r))
    | RX_choice rs ->
        let rs = List.map (convert_regexp ctx) rs in
        wrap (RX_choice rs)
    | RX_seq rs ->
        let rs = List.map (convert_regexp ctx) rs in
        wrap (RX_seq rs)

let rec convert_rule_elem ctx r =
  let lm = AstUtils.infer_mod r.rule_elem_mod in
  let wrap r' = {rule_elem     = r';
                 rule_elem_mod = r.rule_elem_mod;
                 rule_elem_loc = r.rule_elem_loc;
                 rule_elem_aux = r.rule_elem_aux} in
  match r.rule_elem with
    | RE_bitvector v ->
        ctx, wrap (RE_bitvector v)
    | RE_align a ->
        ctx, wrap (RE_align a)
    | RE_pad (p, v) ->
        ctx, wrap (RE_pad (p, v))
    | RE_bitfield id ->
        ctx, wrap (RE_bitfield id)
    | RE_regexp rx ->
        ctx, wrap (RE_regexp (convert_regexp ctx rx))
    | RE_non_term (Modul (Some m), id, None) ->
        let m = Modul (Mod_explicit m) in
        ctx, wrap (RE_non_term (m, id, None))
    | RE_non_term (Modul (Some m), id, Some inhs) ->
        let m = Modul (Mod_explicit m) in
        let inhs = List.map (fun (i, a, e) ->
                       i, a, convert_exp ctx lm e
                     ) inhs in
        ctx, wrap (RE_non_term (m, id, Some inhs))
    | RE_non_term (Modul None, id, None) ->
        let m = mod_of_nonterm ctx lm id in
        ctx, wrap (RE_non_term (m, id, None))
    | RE_non_term (Modul None, id, Some inhs) ->
        let m = mod_of_nonterm ctx lm id in
        let inhs = List.map (fun (i, a, e) ->
                       i, a, convert_exp ctx lm e
                     ) inhs in
        ctx, wrap (RE_non_term (m, id, Some inhs))
    | RE_scan (l, d) ->
        ctx, wrap (RE_scan (l, d))
    | RE_named (v, r) ->
        (* `v` is not bound in `r`; bindings introduced in `r` are
           not visible outside. *)
        let _, r = convert_rule_elem ctx r in
        let locals = StringSet.add (var_name v) ctx.ctx_locals in
        let ctx = {ctx with ctx_locals = locals} in
        ctx, wrap (RE_named (v, r))
    | RE_action a ->
        let a = convert_act ctx lm a in
        ctx, wrap (RE_action a)
    | RE_epsilon ->
        ctx, wrap RE_epsilon
    | RE_constraint c ->
        ctx, wrap (RE_constraint (convert_exp ctx lm c))
    | RE_seq rs ->
        (* bindings introduced in `rs` are not visible outside the
           `RE_seq`. *)
        let _, rs = List.fold_left (fun (ctx, acc) r ->
                        let ctx, r = convert_rule_elem ctx r in
                        ctx, r :: acc
                      ) (ctx, []) rs in
        ctx, wrap (RE_seq (List.rev rs))
    | RE_choice rs ->
        (* bindings introduced in any choice `r` are not visible in
           other choices, and also not visible outside the
           `RE_choice`. *)
        let rs = List.map (fun r -> snd (convert_rule_elem ctx r)) rs in
        ctx, wrap (RE_choice rs)
    | RE_star (r, None) ->
        let _, r = convert_rule_elem ctx r in
        ctx, wrap (RE_star (r, None))
    | RE_star (r, Some e) ->
        let e = convert_exp ctx lm e in
        let _, r = convert_rule_elem ctx r in
        ctx, wrap (RE_star (r, Some e))
    | RE_opt r ->
        let _, r = convert_rule_elem ctx r in
        ctx, wrap (RE_opt r)
    | RE_set_view e ->
        ctx, wrap (RE_set_view (convert_exp ctx lm e))
    | RE_at_pos (e, r) ->
        let e = convert_exp ctx lm e in
        let _, r = convert_rule_elem ctx r in
        ctx, wrap (RE_at_pos (e, r))
    | RE_at_view (e, r) ->
        let e = convert_exp ctx lm e in
        let _, r = convert_rule_elem ctx r in
        ctx, wrap (RE_at_view (e, r))
    | RE_map_views (e, r) ->
        let e = convert_exp ctx lm e in
        let _, r = convert_rule_elem ctx r in
        ctx, wrap (RE_map_views (e, r))
    | RE_seq_flat rs ->
        (* similar to `RE_seq`. *)
        let _, rs = List.fold_left (fun (ctx, acc) r ->
                        let ctx, r = convert_rule_elem ctx r in
                        ctx, r :: acc
                      ) (ctx, []) rs in
        ctx, wrap (RE_seq (List.rev rs))

let convert_rule ctx lm r =
  (* add `_temps` to the local bindings *)
  let ctx, tmps =
    List.fold_left (fun (ctx, tmps) (v, t, e) ->
        let t = convert_type_expr ctx lm t in
        let e = convert_exp ctx lm e in
        let ctx_locals = StringSet.add (var_name v) ctx.ctx_locals in
        {ctx with ctx_locals}, (v, t, e) :: tmps
      ) (ctx, []) r.rule_temps in
  (* the `rhs` is inside an implicit `RE_seq`. *)
  let _, rs = List.fold_left (fun (ctx, acc) r ->
                  let ctx, r = convert_rule_elem ctx r in
                  ctx, r :: acc
                ) (ctx, []) r.rule_rhs in
  {rule_rhs   = List.rev rs;
   rule_temps = List.rev tmps;
   rule_loc   = r.rule_loc}

let convert_attr ctx lm a =
  match a with
    | ALT_type id ->
        ALT_type id
    | ALT_decls ds ->
        let ds = List.map (fun (id, t, x, e) ->
                     let t = convert_type_expr ctx lm t in
                     let e = match e with
                         | Some e -> Some (convert_exp ctx lm e)
                         | None   -> None in
                     id, t, x, e
                   ) ds in
        ALT_decls ds

let convert_ntd ctx nt =
  (* update locals with `varname` and inherited attrs *)
  let ctx = match nt.non_term_varname with
      | Some v ->
          let locals = StringSet.add (var_name v) ctx.ctx_locals in
          {ctx with ctx_locals = locals}
      | None ->
          ctx in
  let lm = AstUtils.infer_mod nt.non_term_mod in
  let ctx, inhs =
    List.fold_left (fun (ctx, inhs) (v, t, x) ->
        let t = convert_type_expr ctx lm t in
        let locals = StringSet.add (var_name v) ctx.ctx_locals in
        {ctx with ctx_locals = locals}, (v, t, x) :: inhs
      ) (ctx, []) nt.non_term_inh_attrs in
  let syns = convert_attr ctx lm nt.non_term_syn_attrs in
  let rls  = List.map (convert_rule ctx lm) nt.non_term_rules in
  {non_term_name      = nt.non_term_name;
   non_term_varname   = nt.non_term_varname;
   non_term_inh_attrs = List.rev inhs;
   non_term_syn_attrs = syns;
   non_term_rules     = rls;
   non_term_mod       = nt.non_term_mod;
   non_term_loc       = nt.non_term_loc}

let convert_fun ctx fd =
  let lm = AstUtils.infer_mod fd.fun_defn_mod in
  (* bind params in local vars *)
  let ctx, ps = List.fold_left (fun (ctx, acc) (v, t, x) ->
                    let vn   = var_name v in
                    let locs = StringSet.add vn ctx.ctx_locals in
                    let ctx  = {ctx with ctx_locals = locs} in
                    let t    = convert_type_expr ctx lm t in
                    ctx, (v, t, x) :: acc
                  ) (ctx, []) fd.fun_defn_params in
  let res = convert_type_expr ctx lm fd.fun_defn_res_type in
  let bdy = convert_exp ctx lm fd.fun_defn_body in
  {fun_defn_ident     = fd.fun_defn_ident;
   fun_defn_tvars     = fd.fun_defn_tvars;
   fun_defn_params    = List.rev ps;
   fun_defn_res_type  = res;
   fun_defn_body      = bdy;
   fun_defn_recursive = fd.fun_defn_recursive;
   fun_defn_synth     = fd.fun_defn_synth;
   fun_defn_mod       = fd.fun_defn_mod;
   fun_defn_loc       = fd.fun_defn_loc;
   fun_defn_aux       = fd.fun_defn_aux}

let convert_recfuns ctx rfd =
  {recfuns     = List.map (convert_fun ctx) rfd.recfuns;
   recfuns_loc = rfd.recfuns_loc}

let convert_const ctx c =
  let lm = AstUtils.infer_mod c.const_defn_mod in
  let t  = convert_type_expr ctx lm c.const_defn_type in
  let v  = convert_exp ctx lm c.const_defn_val in
  {const_defn_ident = c.const_defn_ident;
   const_defn_type  = t;
   const_defn_val   = v;
   const_defn_mod   = c.const_defn_mod;
   const_defn_loc   = c.const_defn_loc;
   const_defn_aux   = c.const_defn_aux}

let convert_format_decl ctx fd =
  let nt = convert_ntd ctx fd.format_decl in
  {format_decl     = nt;
   format_deco     = fd.format_deco;
   format_decl_loc = fd.format_decl_loc}

let convert_format ctx fd =
  {format_decls = List.map (convert_format_decl ctx) fd.format_decls;
   format_loc   = fd.format_loc}

let collect_nonterms ctx pds =
  List.fold_left (fun ctx pd ->
      match pd with
        | PDecl_format f ->
            List.fold_left (fun ctx fd ->
                let n = Location.value fd.format_decl.non_term_name in
                let nonterms = StringSet.add n ctx.ctx_nonterms in
                {ctx with ctx_nonterms = nonterms}
              ) ctx f.format_decls
        | _ ->
            ctx
    ) ctx pds

let rec convert ctx acc pds =
  let ctx = collect_nonterms ctx pds in
  match pds with
    | [] ->
        acc
    | pd :: rest ->
        (match pd with
           | PDecl_include _ ->
               (* This should have been processed and removed. *)
               assert false
           | PDecl_types (ts, l) ->
               let ctx, ts = convert_types ctx ts in
               let d = Decl_types (ts, l) in
               convert ctx (d :: acc) rest
           | PDecl_const c ->
               let d = Decl_const (convert_const ctx c) in
               convert ctx (d :: acc) rest
           | PDecl_fun f ->
               let d = Decl_fun (convert_fun ctx f) in
               convert ctx (d :: acc) rest
           | PDecl_recfuns fs ->
               let d = Decl_recfuns (convert_recfuns ctx fs) in
               convert ctx (d :: acc) rest
           | PDecl_format f ->
               let d = Decl_format (convert_format ctx f) in
               convert ctx (d :: acc) rest)

let convert_spec (b: builtins) (s: (unit, unit) pre_spec_module)
    : (unit, unit) spec_module =
  let decls = convert (init_ctx b) [] s.pre_decls in
  {decls = List.rev decls}
