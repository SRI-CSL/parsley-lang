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

(* Generate the IR for a spec. *)

open Parsing
open Typing
open TypedAst
open Scf

let lower_spec trace (_, init_venv) tenv (spec: spec_module) print_anf =
  (* VEnv creates globally unique bindings for all variables bound in
     the spec; however, the predefined/builtin variables from the
     standard library are not bound in the spec, so the VEnv needs to
     be initialized to include them.  For this it uses the init_venv
     created by the type inferencer, which is already seeded with the
     tagged variables from the standard library. *)
  let venv = TypeInfer.VEnv.fold_left (fun venv v ->
                 let _, venv = Anf.VEnv.bind venv v in
                 venv
               ) Anf.VEnv.empty init_venv in
  let gl = Location.ghost_loc in
  (* Initialize the re (i.e. compiled regexp) environment. *)
  let re_env =
    List.fold_left (fun acc (s, cc) ->
        let re = Dfa.Dfa_of_regexp.re_of_character_class cc in
        Dfa.Automaton.StringMap.add s (gl, re) acc
      ) Dfa.Automaton.StringMap.empty TypeAlgebra.character_classes in

  (* Initialize the IR generation context by allocating a top-level
     frame. *)
  let frame_gen = Anf.mk_frame_id_gen () in
  let site_gen  = Site.mk_id_gen () in
  let init_frame = frame_gen () in
  let ctx = {ctx_tenv       = tenv;
             ctx_toc        = ValueMap.empty;
             ctx_venv       = venv;
             ctx_re_env     = re_env;
             ctx_bitmode    = false;
             ctx_frame      = init_frame;
             ctx_stack      = [init_frame];
             ctx_frame_gen  = frame_gen;
             ctx_mutations  = FrameMap.empty;
             ctx_free_vars  = StringMap.empty;
             ctx_site_gen   = site_gen;
             ctx_site_map   = Site.SiteMap.empty;
             ctx_id_gen     = mk_id_gen ()} in

  (* Create a block for evaluating the statics, i.e. constants and
     function definitions.  It will form the entry block for the
     spec. *)
  let sts = init_block in

  (* Add a function to the function block. *)
  let add_fun ctx fb af =
    let Anf.{afun_ident  = fv;
             afun_params = params;
             afun_body   = afb;
             afun_vars   = vars;
             afun_mod    = m;
             afun_loc    = loc; _} = af in
    let li =
      (* all functions (including synthesized ones) are module exports. *)
      let mn = Location.mk_loc_val m fv.v_loc in
      let fn = Location.mk_loc_val (fst fv.v) fv.v_loc in
      L_assign_mod_fun (mn, fn, params, afb, vars) in
    let id = ctx.ctx_id_gen () in
    add_instr (mk_l2b li afb.aexp_typ loc id None) fb in

  (* Process the spec in lexical order. *)
  let ctx, _, sts, foreigns =
    List.fold_left (fun (ctx, tvenv, sts, foreigns) d ->
        match d with
          | Ast.Decl_types _ ->
              ctx, tvenv, sts, foreigns
          | Ast.Decl_const c ->
              (* populate the consts block *)
              let c', ctx = Scf_of_rule.norm_const ctx c in
              if   print_anf
              then Anf_printer.print_const c';
              let Anf.{aconst_var = v';
                       aconst_val = ae;
                       aconst_mod = m;
                       aconst_loc = loc; _} = c' in
              let mn = Location.mk_loc_val m loc in
              let vn = Location.mk_loc_val (fst v'.v) v'.v_loc in
              let li = L_assign_mod_var (mn, vn, ae) in
              let id = ctx.ctx_id_gen () in
              let sts = add_instr (mk_l2b li ae.aexp_typ loc id None) sts in
              ctx, tvenv, sts, foreigns
          | Ast.Decl_fun f ->
              (* populate the funcs block *)
              let af, ctx = Scf_of_rule.norm_fun ctx f in
              if   print_anf
              then Anf_printer.print_fun af;
              let sts = add_fun ctx sts af in
              ctx, tvenv, sts, foreigns
          | Ast.Decl_recfuns r ->
              (* populate the funcs block *)
              let afs, ctx = Scf_of_rule.norm_recfuns ctx r.recfuns in
              if   print_anf
              then List.iter Anf_printer.print_fun afs;
              let sts = List.fold_left (add_fun ctx) sts afs in
              ctx, tvenv, sts, foreigns
          | Ast.Decl_foreign fs ->
              let foreigns = List.fold_left (fun fs f ->
                                 let m = Anf_common.M_name Ast.(f.ffi_decl_mod) in
                                 let v = Ast.var_name Ast.(f.ffi_decl_ident) in
                                 assert (not (ValueMap.mem (m, v) foreigns));
                                 ValueMap.add (m, v) f fs
                               ) foreigns fs in
              ctx, tvenv, sts, foreigns
          | Ast.Decl_format f ->
              (* generate the CFG blocks for the non-terminals *)
              let ctx, tvenv, sts =
                List.fold_left (fun (ctx, tvenv, sts) (fd: format_decl) ->
                    let ntd = fd.format_decl in
                    let ctx, tvenv = Scf_of_rule.lower_ntd trace ctx tvenv ntd in
                    ctx, tvenv, sts
                  ) (ctx, tvenv, sts) f.format_decls in
              ctx, tvenv, sts, foreigns
      ) (ctx, init_venv, sts, ValueMap.empty) spec.decls in
  let spec =
    {scf_globals  = ctx.ctx_toc;
     scf_statics  = seal_block sts;
     scf_foreigns = foreigns;
     scf_tenv     = ctx.ctx_tenv;
     scf_venv     = ctx.ctx_venv} in

  (* Check consistency of the IR. *)

  if   trace
  then (Printf.printf "%! Original spec:\n%!";
        Scf_printer.print_spec spec);
  Scf_validator.validate spec trace;

  spec
