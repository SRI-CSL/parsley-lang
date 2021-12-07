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

(* Convert a spec into its CFG/ANF form *)

open Parsing
open Typing
open Flow
open Cfg

let lower_spec (_, init_venv) tenv (spec: program) =
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

  (* Initialize the re (i.e. compiled regexp) environment *)
  let re_env =
    let gl = Location.ghost_loc in
    List.fold_left (fun acc (s, cc) ->
        let re = Cfg_regexp.re_of_character_class cc in
        Dfa.StringMap.add s (gl, re) acc
      ) Dfa.StringMap.empty TypeAlgebra.character_classes in

  (* initialize the context with a dummy failure label *)
  let init_failcont = Label.fresh_label () in
  let ctx = {ctx_tenv       = tenv;
             ctx_toc        = FormatToC.empty;
             ctx_ir         = FormatIR.empty;
             ctx_venv       = venv;
             ctx_failcont   = init_failcont;
             ctx_re_env     = re_env} in

  (* create the first block for constant evaluation. its label will be
     the start label for the spec *)
  let _, cb = Cfg_rule.new_block () in
  let _, fb = Cfg_rule.new_block () in

  (* add a function to the function block *)
  let add_fun fb af =
    let Anf.{afun_ident = f';
             afun_body = afb;
             afun_loc = loc; _} = af in
    let v = Anf.make_var f' afb.aexp_typ loc in
    let nd = N_assign_fun (v, af) in
    Cfg_rule.add_gnode fb nd afb.aexp_typ loc in

  (* process the spec in lexical order *)
  let ctx, cb, fb =
    List.fold_left (fun (ctx, cb, fb) d ->
        match d with
          | Ast.Decl_types _ ->
              ctx, cb, fb
          | Ast.Decl_const c ->
              (* populate the consts block *)
              let c', venv =
                Anf_exp.normalize_const ctx.ctx_tenv ctx.ctx_venv c in
              let Anf.{aconst_ident = v';
                       aconst_val = ae;
                       aconst_loc = loc; _} = c' in
              let v = Anf.make_var v' ae.aexp_typ loc in
              let nd = N_assign (v, true, ae) in
              let cb = Cfg_rule.add_gnode cb nd ae.aexp_typ loc in
              {ctx with ctx_venv = venv}, cb, fb
          | Ast.Decl_fun f ->
              (* populate the funcs block *)
              let af, venv =
                Anf_exp.normalize_fun ctx.ctx_tenv ctx.ctx_venv f in
              let fb = add_fun fb af in
              {ctx with ctx_venv = venv}, cb, fb
          | Ast.Decl_recfuns r ->
              (* populate the funcs block *)
              let afs, venv = Anf_exp.normalize_recfuns ctx.ctx_tenv
                                ctx.ctx_venv r.recfuns in
              let fb = List.fold_left add_fun fb afs in
              {ctx with ctx_venv = venv}, cb, fb
          | Ast.Decl_format f ->
              (* generate the CFG blocks for the non-terminals *)
              List.fold_left (fun (ctx, cb, fb) (fd: format_decl) ->
                  let ntd = fd.format_decl in
                  let ctx = Cfg_rule.lower_ntd ctx ntd in
                  ctx, cb, fb
                ) (ctx, cb, fb) f.format_decls
      ) (ctx, cb, fb) spec.decls in
  {ir_toc    = ctx.ctx_toc;
   ir_blocks = ctx.ctx_ir;
   ir_consts = cb;
   ir_funcs  = fb;
   ir_init_failcont = init_failcont}
