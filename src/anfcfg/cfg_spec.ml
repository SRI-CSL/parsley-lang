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
open Cfg

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

  (* Initialize the context with a dummy failure label. *)
  let init_failcont = fresh_virtual () in
  let ctx = {ctx_tenv       = tenv;
             ctx_gtoc       = ValueMap.empty;
             ctx_cfg        = LabelMap.empty;
             ctx_venv       = venv;
             ctx_failcont   = init_failcont;
             ctx_re_env     = re_env;
             ctx_bitmode    = false} in

  (* Create a block for evaluating the statics, i.e. constants and
     function definitions.  Its label will be the start label for the
     spec. *)
  let _, sts = Cfg_rule.new_block gl in

  (* Add a function to the function block. *)
  let add_fun fb af =
    let Anf.{afun_ident  = fv;
             afun_params = params;
             afun_body   = afb;
             afun_vars   = vars;
             afun_mod    = m;
             afun_loc    = loc; _} = af in
    let nd =
      (* all functions (including synthesized ones) are module exports. *)
      let mn = Location.mk_loc_val m fv.v_loc in
      let fn = Location.mk_loc_val (fst fv.v) fv.v_loc in
      N_assign_mod_fun (mn, fn, params, afb, vars) in
    Cfg_rule.add_gnode fb nd afb.aexp_typ loc in

  (* Process the spec in lexical order. *)
  let ctx, _, sts, foreigns =
    List.fold_left (fun (ctx, tvenv, sts, foreigns) d ->
        match d with
          | Ast.Decl_types _ ->
              ctx, tvenv, sts, foreigns
          | Ast.Decl_const c ->
              (* populate the consts block *)
              let c', venv =
                Anf_exp.normalize_const ctx.ctx_tenv ctx.ctx_venv c in
              if   print_anf
              then Anf_printer.print_const c';
              let Anf.{aconst_ident = v';
                       aconst_val = ae;
                       aconst_mod = m;
                       aconst_loc = loc; _} = c' in
              let mn = Location.mk_loc_val m loc in
              let vn = Location.mk_loc_val (fst v') loc in
              let nd = N_assign_mod_var (mn, vn, ae) in
              let sts = Cfg_rule.add_gnode sts nd ae.aexp_typ loc in
              {ctx with ctx_venv = venv}, tvenv, sts, foreigns
          | Ast.Decl_fun f ->
              (* populate the funcs block *)
              let af, venv =
                Anf_exp.normalize_fun ctx.ctx_tenv ctx.ctx_venv f in
              if   print_anf
              then Anf_printer.print_fun af;
              let sts = add_fun sts af in
              {ctx with ctx_venv = venv}, tvenv, sts, foreigns
          | Ast.Decl_recfuns r ->
              (* populate the funcs block *)
              let afs, venv = Anf_exp.normalize_recfuns ctx.ctx_tenv
                                ctx.ctx_venv r.recfuns in
              if   print_anf
              then List.iter Anf_printer.print_fun afs;
              let sts = List.fold_left add_fun sts afs in
              {ctx with ctx_venv = venv}, tvenv, sts, foreigns
          | Ast.Decl_foreign fs ->
              let foreigns = List.fold_left (fun fs f ->
                                 let m = Anf.M_name Ast.(f.ffi_decl_mod) in
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
                    let ctx, tvenv = Cfg_rule.lower_ntd trace ctx tvenv ntd in
                    ctx, tvenv, sts
                  ) (ctx, tvenv, sts) f.format_decls in
              ctx, tvenv, sts, foreigns
      ) (ctx, init_venv, sts, ValueMap.empty) spec.decls in
  let spec =
    {cfg_gtoc          = ctx.ctx_gtoc;
     cfg_blocks        = ctx.ctx_cfg;
     cfg_statics       = sts;
     cfg_foreigns      = foreigns;
     cfg_init_failcont = init_failcont;
     cfg_tenv          = ctx.ctx_tenv;
     cfg_venv          = ctx.ctx_venv} in

  (* Check consistency of the IR. *)
  if   trace
  then (Printf.printf "%! Original spec:\n%!";
        Cfg_printer.print_spec spec);
  Cfg_optimize.validate spec false trace;

  (* Optimize the IR, and then connect back-pointers in the CFG. *)
  let opt_spec = Cfg_optimize.optimize spec trace in
  let opt_spec = Cfg_optimize.connect_predecessors opt_spec in

  (* Check consistency of optimized IR. *)
  if   trace
  then (Printf.printf "%! Optimized spec:\n%!";
        Cfg_printer.print_spec opt_spec);
  Cfg_optimize.validate opt_spec true trace;

  (* Return the optimized spec. *)
  opt_spec
