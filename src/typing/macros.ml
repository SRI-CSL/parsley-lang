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

(* This file implements the "macro" system.

   Parsley is a first-order language with some standard data
   structures that benefit from higher-order operations: maps and
   folds operations over structures such as lists, sets and maps.  The
   type-signature for these operations are provided in the standard
   library.

   These higher-order operations are implemented via invocations to
   synthesized functions:

       List.map(func, lst)  -=->  __list_map_func__(lst, [])

   where -=-> indicates rewrite and `__list_map_func__` is
   effectively defined as:

    recfun __list_map_func__(lst: [s], acc: [t]) -> [t] = {
        (case lst of
         | []     -> List.rev(acc)
         | h :: t -> __list_map_func__(t, func(h) :: acc)
        )
    }

   where `s -> t` is the type signature of `func`.  This ensures that
   the usage of `func` remains first-order.

   Similarly,

       List.map2(func, al, bl) -=-> __list_map2_func__(al, bl, [])

   where

    recfun __list_map2_func__(al: [s], bl: [t], l:[u]) -> [u] = {
        (case (al, bl) of
         | ([], [])             -> List.rev(l)
         | (ah :: at, bh :: bt) -> __list_map2_func__(at, bt,
                                                      func(ah, bh) :: l)
        )
    }

   Handling a specific call to a higher-order operation as a macro
   thus involves two steps:

   . synthesizing a new specialized function for the call

   . replacing the call by an equivalent call to the specialized
     function

   We would like to type-check the synthesized function and the
   replacement equivalent call, which means that the macro expansion
   must be performed before type-checking, i.e. it must work with the
   raw ast.

   The synthesized functions need to be inserted at the appropriate
   point into the spec:  in the first example above,
   '__list_map_func__' needs to appear after the definition of 'func'
   but before the higher-order invocation of 'func'.  To do this, all
   the synthesized functions are collected, and each one is inserted
   just after the corresponding 'func'.

   In order to catch all invocations of `List.map` and similar
   functions, we do not allow them to be bound to variables, otherwise
   they would be hidden from the scan.

   The applied 'func' could be of two types:

   . if it is a user-defined function, it will have a user-specified
     definition, which we will need to extract from the AST.

   . if it is a standard-library function, it will have a signature
     specified in typeAlgebra.

   During the AST scan, the following information is collected:

   . each function definition is collected in case it is used at
     higher-order, and indexed for lookup by name.  Its body is
     scanned looking for macro invocations; if found, the invocation
     is handled as described below.

   . each constant's definition body is scanned for macro
     invocations, and any that are found are handled as below.

   . after all the functions and constants, any macro invocation
     occuring in any expression occuring in the grammar sublanguage
     are handled.  This is done in a second pass through the spec.

   Each invocation is handled as follows:

   . if a function has not been synthesized already for that
     invocation type (by looking in a synthesis cache), it's
     definition is synthesized and added to the cache.

     The invocation is replaced by an equivalent call to the
     synthesized function.

   After all invocations are handled, the definition for each
   synthesized function is inserted into the spec right after the
   corresponding function it was synthesized for.  This results in an
   AST that is ready for type-checking.
 *)

open Parsing
open Ast
open TypingExceptions

(* Function synthesis from templates:

  For each higher-order construct, we keep a template for the
  synthesized function.  For example, for List.map, we have

  recfun <list_map_tmpl> <'s, 't> (lst: ['s], acc: ['t]) -> ['t] = {
    (case lst of
     | []     -> List.rev(acc)
     | h :: t -> <list_map_tmpl> (t, <f>(h) :: acc)
    )
  }

  where <f> will be substituted by the actual function name 'func',
  and <list_map_tmpl> by the synthesized name.

  The synthesis will also require the type variables <'s, 't> to be
  substituted using the type signature of 'func'.  This is
  straightforward if 'func' is monomorphic: 's and 't are simply
  substituted with the corresponding monomorphic type.

  However, for polymorphic 'func', this will require matching
  polymorphic types. For example, if 'func' has signature

    <'a> func: 'a -> 'a

  then the substitution will be 's => 'a, 't => 'a, and the
  synthesized result will be polymorphic over <'a>.  Similarly, if
  'func' has signature

    <a', 'b> func: list<'a> -> set<'b>

  then the substitution will be 's => list<'a>, 't => set<'b>, and the
  synthesized result will polymorphic over <'a, 'b>.

 *)

(* A function that is applied at higher order is either a user defined
   function (None, f) or a function from a stdlib module (Some m, f) *)
type fname = ident option * ident

(* type signature of a function or builtin *)
type fsig =
  (* type vars x param types x result type *)
  tvar list * type_expr list * type_expr

(* information about a higher-order invocation *)
type hoi =
  {hoi_name:      fname;           (* stdname fname     *)
   hoi_hoimloc:   Location.t;      (* stdlib module     *)
   hoi_hoifloc:   Location.t;      (* stdlib function   *)
   hoi_hoimfloc:  Location.t;      (* mod.func location *)
   hoi_fname:     fname;           (* invoked function  *)
   hoi_fsig:      fsig;            (* invoked signature *)
   hoi_arglocs:   Location.t list; (* call arguments    *)
   hoi_retloc:    Location.t;      (* location of full invocation *)
   hoi_synthname: string;          (* synthesized function name   *)
   hoi_synthsig:  fsig}            (* synthesized signature       *)

(* Each invocation site results in a possible function synthesis.  To
   ensure that we don't re-synthesize the same function, we track
   synthesized functions by their unique name, which in turn is
   synthesized from the following components concatenated together
   with '__':

     . stdlib invocation (modname__apiname)
     . applied function  (funcname)
     . the type signature of the synthesized function

   The latter is needed since the applied function could be
   polymorphic, and could be used with a stdlib invocation at
   different types.
 *)

module SynthCache = Map.Make(String)
type synth_cache  = (hoi * (unit, unit) fun_defn) SynthCache.t

(* utility converters *)

let string_of_fname (fn: fname) : string =
  match fn with
    | None, f -> Location.value f
    | Some m, f -> Location.value m ^ "." ^ Location.value f

let var_of_ident (i: ident) : unit var =
  let v = Location.value i in
  Location.mk_loc_val (v, ()) (Location.loc i)

let ident_of_var (v: unit var) : ident =
  let i, _ = Location.value v in
  Location.mk_loc_val i (Location.loc v)

(* utility constructors *)

let mk_texpr t l =
  {type_expr = t;
   type_expr_loc = l}

let mk_list_of arg =
  let lst =
    let ltv = Location.mk_loc_val "[]" arg.type_expr_loc in
    mk_texpr (TE_tvar ltv) arg.type_expr_loc in
  mk_texpr (TE_tapp (lst, [arg])) arg.type_expr_loc

let mk_var s l =
  Location.mk_loc_val (s, ()) l

let mk_expr e l =
  {expr = e;
   expr_loc = l;
   expr_aux = ()}

let mk_pat p l =
  {pattern = p;
   pattern_loc = l;
   pattern_aux = ()}

let mk_empty_list loc =
  let t = Location.mk_loc_val "[]" loc in
  let c = Location.mk_loc_val "[]" loc in
  {expr     = E_constr ((t, c), []);
   expr_loc = loc;
   expr_aux = ()}

(* name and type stringification *)

let stringify_fname fn =
  match fn with
    | None, f ->
        Location.value f
    | Some m, f ->
        let s = Location.value m ^ "_" ^ Location.value f in
        String.lowercase_ascii s

let rec stringify_type_expr te =
  match te.type_expr with
    | TE_tvar tv ->
        Location.value tv
    | TE_tapp (c, []) ->
        stringify_type_expr c
    | TE_tapp ({type_expr = TE_tvar tv;_}, args)
         when Location.value tv = "[]" ->
        "["
        ^ (String.concat "_" (List.map stringify_type_expr args))
        ^ "]"
    | TE_tapp (c, args) ->
        stringify_type_expr c
        ^ "<"
        ^ (String.concat "_" (List.map stringify_type_expr args))
        ^ ">"

let stringify_fsig (tvs, args, ret) =
  String.concat "##"
    [String.concat "_" (List.map Location.value tvs);
     String.concat "__" (List.map stringify_type_expr args);
     stringify_type_expr ret]

(* An invocation of a higher-order construct results in a first-order
   function being synthesized; there is a synthesizer function for
   each such higher-order construct. *)

let synth_list_map hoi =
  (* locations *)
  assert (List.length hoi.hoi_arglocs = 1);
  let lstloc = List.hd hoi.hoi_arglocs in
  let accloc = hoi.hoi_retloc in
  (* synthesized signature *)
  let stvs, stargs, stret = hoi.hoi_synthsig in
  (* type expressions *)
  let lstt = List.hd stargs in
  let lttt = List.hd (List.tl stargs) in
  (* variables *)
  let lstv = mk_var "lst" lstloc in
  let accv = mk_var "acc" accloc in
  let lst  = mk_expr (E_var lstv) lstloc in
  let acc  = mk_expr (E_var accv) accloc in
  (* List.rev *)
  let lrev =
    let m = Location.mk_loc_val "List" hoi.hoi_hoimloc in
    let f = Location.mk_loc_val "rev"  hoi.hoi_hoifloc in
    mk_expr (E_mod_member (m, f)) hoi.hoi_hoimfloc in
  (* List.rev(acc) *)
  let lrev_acc = mk_expr (E_apply (lrev, [acc])) accloc in
  (* pattern variables *)
  let hv  = mk_var "h"  lstloc in
  let tlv = mk_var "tl" lstloc in
  let h   = mk_pat (P_var hv) lstloc in
  let tl  = mk_pat (P_var tlv) lstloc in
  (* patterns *)
  (* [] *)
  let m = Location.mk_loc_val "[]" lstloc in
  let c = Location.mk_loc_val "[]" lstloc in
  let empty = mk_pat (P_variant ((m, c), [])) lstloc in
  (* h :: t *)
  let c = Location.mk_loc_val "::" lstloc in
  let cons = mk_pat (P_variant ((m, c), [h; tl])) lstloc in
  (* build the recursive call: _list_map_func_(tl, func(h) :: acc) *)
  let h    = mk_expr (E_var hv)  lstloc in
  let tl   = mk_expr (E_var tlv) lstloc in
  let func = match hoi.hoi_fname with
      | None, f ->
          mk_expr (E_var (var_of_ident f)) (Location.loc f)
      | Some m, f ->
          mk_expr (E_mod_member (m, f))
            (Location.extent (Location.loc m) (Location.loc f)) in
  let acc_arg =
    mk_expr (E_constr ((m, c),
                       [mk_expr (E_apply (func, [h])) func.expr_loc;
                        acc])) accloc in
  let reccall =
    let f = mk_var hoi.hoi_synthname func.expr_loc in
    mk_expr (E_apply ((mk_expr (E_var f) func.expr_loc),
                      [tl; acc_arg]))
      accloc in
  (* case expression *)
  let case =
    mk_expr (E_case (lst, [empty, lrev_acc;
                           cons,  reccall])) accloc in
  let fun_ident = Location.mk_loc_val hoi.hoi_synthname accloc in
  {fun_defn_ident     = var_of_ident fun_ident;
   fun_defn_tvars     = stvs;
   fun_defn_params    = [lstv, lstt; accv, lttt];
   fun_defn_res_type  = stret;
   fun_defn_body      = case;
   fun_defn_recursive = true;
   fun_defn_synth     = true;
   fun_defn_loc       = Location.ghost_loc;
   fun_defn_aux       = ()}

let synth_list_map2 hoi =
  (* locations.  use ghost locations for tuples *)
  assert (List.length hoi.hoi_arglocs = 2);
  let asloc, bsloc = match hoi.hoi_arglocs with
      | a :: b :: _ -> a, b
      | _ -> assert false in
  let lloc = hoi.hoi_retloc in
  (* synthesized signature *)
  let stvs, stargs, stret = hoi.hoi_synthsig in
  (* type expressions *)
  let lst, tl  = List.hd stargs, List.tl stargs in
  let ltt, tl  = List.hd tl, List.tl tl in
  let lut  = List.hd tl in
  (* variables *)
  let alv  = mk_var "al" asloc in
  let blv  = mk_var "bl" bsloc in
  let lv   = mk_var "l"  lloc in
  let al   = mk_expr (E_var alv) asloc in
  let bl   = mk_expr (E_var blv) bsloc in
  let l    = mk_expr (E_var lv)  lloc in
  (* List.rev *)
  let lrev =
    let m = Location.mk_loc_val "List" hoi.hoi_hoimloc in
    let f = Location.mk_loc_val "rev"  hoi.hoi_hoifloc in
    mk_expr (E_mod_member (m, f)) hoi.hoi_hoimfloc in
  (* List.rev(l) *)
  let lrev_acc = mk_expr (E_apply (lrev, [l])) lloc in
  (* pattern variables *)
  let ahv = mk_var "ah" asloc in
  let atv = mk_var "at" asloc in
  let bhv = mk_var "bh" bsloc in
  let btv = mk_var "bt" bsloc in
  let ah  = mk_pat (P_var ahv) asloc in
  let at  = mk_pat (P_var atv) asloc in
  let bh  = mk_pat (P_var bhv) bsloc in
  let bt  = mk_pat (P_var btv) bsloc in
  (* patterns *)
  (* ([],[]) *)
  let am = Location.mk_loc_val "[]" asloc in
  let ac = Location.mk_loc_val "[]" asloc in
  let aempty = mk_pat (P_variant ((am, ac), [])) asloc in
  let bm = Location.mk_loc_val "[]" bsloc in
  let bc = Location.mk_loc_val "[]" bsloc in
  let bempty = mk_pat (P_variant ((bm, bc), [])) bsloc in
  let tm = Location.mk_loc_val "*" Location.ghost_loc in
  let tc = Location.mk_loc_val "_Tuple" Location.ghost_loc in
  let empty = mk_pat (P_variant ((tm, tc), [aempty; bempty]))
                Location.ghost_loc in
  (* ah :: at, bh :: bt *)
  let ac = Location.mk_loc_val "::" asloc in
  let bc = Location.mk_loc_val "::" bsloc in
  let acons = mk_pat (P_variant ((am, ac), [ah; at])) asloc in
  let bcons = mk_pat (P_variant ((bm, bc), [bh; bt])) bsloc in
  let full  = mk_pat (P_variant ((tm, tc), [acons; bcons]))
                Location.ghost_loc in
  (* other cases *)
  let wild  = mk_pat P_wildcard Location.ghost_loc in
  (* build the recursive call: _list_map2_func_(at, bt, func(ah, bh) :: l) *)
  let ah   = mk_expr (E_var ahv) asloc in
  let at   = mk_expr (E_var atv) asloc in
  let bh   = mk_expr (E_var bhv) bsloc in
  let bt   = mk_expr (E_var btv) bsloc in
  let func = match hoi.hoi_fname with
      | None, f ->
          mk_expr (E_var (var_of_ident f)) (Location.loc f)
      | Some m, f ->
          mk_expr (E_mod_member (m, f))
            (Location.extent (Location.loc m) (Location.loc f)) in

  let lm = Location.mk_loc_val "[]" lloc in
  let lc = Location.mk_loc_val "::" lloc in
  let acc_arg =
    mk_expr (E_constr ((lm, lc),
                       [mk_expr (E_apply (func, [ah; bh])) func.expr_loc;
                        l])) lloc in
  let reccall =
    let f = mk_var hoi.hoi_synthname func.expr_loc in
    mk_expr (E_apply ((mk_expr (E_var f) func.expr_loc),
                      [at; bt; acc_arg]))
      lloc in
  (* case (al, bl) ... *)
  let discr = mk_expr (E_constr ((tm, tc), [al; bl]))
                Location.ghost_loc in
  let case =
    mk_expr (E_case (discr, [empty, lrev_acc;
                             full,  reccall;
                             wild,  lrev_acc])) lloc in
  let fun_ident = Location.mk_loc_val hoi.hoi_synthname lloc in
  {fun_defn_ident     = var_of_ident fun_ident;
   fun_defn_tvars     = stvs;
   fun_defn_params    = [alv, lst; blv, ltt; lv, lut];
   fun_defn_res_type  = stret;
   fun_defn_body      = case;
   fun_defn_recursive = true;
   fun_defn_synth     = true;
   fun_defn_loc       = Location.ghost_loc;
   fun_defn_aux       = ()}


(* Each higher-order invocation needs to be replaced by a call to
   the synthesized function.  The replacer functions construct this
   replacement call.  The `args` to these functions contain only the
   non-functional arguments from the original invocation. *)

let replace_list_map hoi args : (unit, unit) expr =
  assert (List.length args = 1);
  let fv = mk_var hoi.hoi_synthname hoi.hoi_retloc in
  let fn = mk_expr (E_var fv) hoi.hoi_retloc in
  let args = args @ [mk_empty_list hoi.hoi_retloc] in
  mk_expr (E_apply (fn, args)) hoi.hoi_retloc

let replace_list_map2 hoi args : (unit, unit) expr =
  assert (List.length args = 2);
  let fv = mk_var hoi.hoi_synthname hoi.hoi_retloc in
  let fn = mk_expr (E_var fv) hoi.hoi_retloc in
  let args = args @ [mk_empty_list hoi.hoi_retloc] in
  mk_expr (E_apply (fn, args)) hoi.hoi_retloc

(** Scan the specification looking for higher-order invocations, and
    expand any invocations found. **)

module StringMap = Map.Make(String)
module StdlibMap = Map.Make(struct type t = string * string
                                   let compare = compare
                            end)

type builtin = TypeAlgebra.builtin_dataconstructor

type context =
  {(* user-defined function definitions seen so far *)
   ctx_fdefs:  (unit, unit) fun_defn StringMap.t;
   (* stdlib functions *)
   ctx_stddefs: builtin StdlibMap.t;
   (* increment to synthesized functions *)
   ctx_synths: (unit, unit) fun_defn list;
   (* synthesis cache *)
   ctx_cache: synth_cache}

let fsig_of_fun_defn d : fsig =
  (d.fun_defn_tvars,
   List.map snd d.fun_defn_params,
   d.fun_defn_res_type)

let fsig_of_builtin (_, tvars, sg) : fsig =
  let mk_tvar (TName t) =
    Location.mk_loc_val t Location.ghost_loc in
  let tvs = List.map mk_tvar tvars in
  let args = AstUtils.arrow_args sg in
  let res, params = match List.rev args with
      | h :: tl -> h, List.rev tl
      | _ -> assert false in
  (tvs, params, res)

(* the top-level macro-expander *)
let expand_call ctx ((m, i, l), rl) (args: (unit, unit) expr list)
    : context * (unit, unit) expr =
  (* The first argument should be the invoked function.  It must be
     either a symbol for a user-defined function, or a function from a
     standard library module; any other expression is illegal. *)
  let get_func a : fname * fsig =
    match a.expr with
      | E_var v ->
          let fid = ident_of_var v in
          let fn  = Location.value fid in
          (match StringMap.find_opt fn ctx.ctx_fdefs with
             | Some fd ->
                 (None, fid), fsig_of_fun_defn fd
             | None ->
                 let err = UnboundIdentifier (a.expr_loc, fn) in
                 raise (Error err))
      | E_mod_member (m, f) ->
          let mn, fn = Location.value m, Location.value f in
          (match StdlibMap.find_opt (mn, fn) ctx.ctx_stddefs with
             | Some d ->
                 (Some m, f), fsig_of_builtin d
             | None ->
                 let err = UnknownModItem (a.expr_loc, MName mn, DName fn) in
                 raise (Error err))
      | _ ->
          raise (Error (IllegalFunctionArgument (m, i))) in
  let mk_synth_name hoi_prefix fname ssig =
    hoi_prefix ^ stringify_fname fname ^ "_" ^ stringify_fsig ssig in
  let (fname, fsig), (sname, ssig), args, synther, replacer =
    match Location.value m, Location.value i with
      | "List", "map" ->
          let nargs = List.length args in
          (if nargs != 2
           then let err = FunctionCallArity (l, "List.map", 2, nargs) in
                raise (Error err));
          let fname, fsig = get_func (List.hd args) in
          let mk_synth_sig (tvs, args, ret) =
            let nargs = List.length args in
            if nargs != 1
            then let f = string_of_fname fname in
                 let err = IncompatibleArityFunctionArgument
                             (rl, "List.map", 1, f, nargs) in
                 raise (Error err)
            else (tvs, [mk_list_of (List.hd args);
                        mk_list_of ret], (* accumulator *)
                  mk_list_of ret) in
          let ssig  = mk_synth_sig fsig in
          let sname = mk_synth_name "_list_map_" fname ssig in
          (fname, fsig), (sname, ssig), List.tl args,
          synth_list_map, replace_list_map
      | "List", "map2" ->
          let nargs = List.length args in
          (if nargs != 3
           then let err = FunctionCallArity (l, "List.map2", 3, nargs) in
                raise (Error err));
          let fname, fsig = get_func (List.hd args) in
          let mk_synth_sig (tvs, args, ret) =
            let nargs = List.length args in
            if nargs != 2
            then let f = string_of_fname fname in
                 let err = IncompatibleArityFunctionArgument
                             (rl, "List.map2", 2, f, nargs) in
                 raise (Error err)
            else let a = List.hd args in
                 let b = List.hd (List.tl args) in
                 (tvs, [mk_list_of a;
                        mk_list_of b;
                        mk_list_of ret], (* accumulator *)
                  mk_list_of ret) in
          let ssig = mk_synth_sig fsig in
          let sname = mk_synth_name "_list_map2_" fname ssig in
          (fname, fsig), (sname, ssig), List.tl args,
          synth_list_map2, replace_list_map2
      | _ ->
          assert false in
  let hoi = {hoi_name       = Some m, i;
             hoi_hoimloc    = Location.loc m;
             hoi_hoifloc    = Location.loc i;
             hoi_hoimfloc   = l;
             hoi_fname      = fname;
             hoi_fsig       = fsig;
             hoi_arglocs    = List.map (fun e -> e.expr_loc) args;
             hoi_retloc     = rl;
             hoi_synthsig   = ssig;
             hoi_synthname  = sname} in
  let ctx = if SynthCache.mem sname ctx.ctx_cache
            then ctx
            else let sf = synther hoi in
                 let ctx_cache =
                   SynthCache.add sname (hoi, sf) ctx.ctx_cache in
                 let ctx_synths = sf :: ctx.ctx_synths in
                 {ctx with ctx_cache; ctx_synths} in
  ctx, replacer hoi args

(* scan and expand expression nodes.

   `E_apply`, `E_let` and `E_case` nodes are the ones of interest:
   invocations will be in `E_apply`, while we want to make sure no
   higher-order constructs are bound in the binding nodes `E_let` and
   `E_case`, otherwise we won't see them in the `E_apply` nodes.
 *)

let rec check_ho_binding def =
  match def.expr with
    | E_mod_member (m, i) ->
        if TypeAlgebra.is_higher_order (m, i)
        then raise (Error (IllegalBinding (m, i)))
    | E_constr (_, args) ->
        ignore (List.map check_ho_binding args)
    (* Remember to also look under records if we add support for
       record patterns *)
    | E_cast (e, _) ->
        check_ho_binding e
    | _ ->
        ()

let rec expand_expr ctx (exp: (unit, unit) expr)
        : context * (unit, unit) expr =
  match exp.expr with
    | E_var _ | E_literal _ | E_mod_member _ ->
        ctx, exp
    | E_constr (c, es) ->
        let ctx, es = expand_exprs ctx es in
        ctx, {exp with expr = E_constr (c, es)}
    | E_record fs ->
        let ctx, fs =
          List.fold_left (fun (ctx, fs) (f, e) ->
              let ctx, e = expand_expr ctx e in
              ctx, (f, e) :: fs
            ) (ctx, []) fs in
        ctx, {exp with expr = E_record (List.rev fs)}
    | E_unop (op, e) ->
        let ctx, e = expand_expr ctx e in
        ctx, {exp with expr = E_unop(op, e)}
    | E_binop (op, l, r) ->
        let ctx, l = expand_expr ctx l in
        let ctx, r = expand_expr ctx r in
        ctx, {exp with expr = E_binop(op, l, r)}
    | E_recop (t, op, e) ->
        let ctx, e = expand_expr ctx e in
        ctx, {exp with expr = E_recop (t, op, e)}
    | E_bitrange (e, f, l) ->
        let ctx, e = expand_expr ctx e in
        ctx, {exp with expr = E_bitrange (e, f, l)}
    | E_match (e, m) ->
        let ctx, e = expand_expr ctx e in
        ctx, {exp with expr = E_match (e, m)}
    | E_field (e, f) ->
        let ctx, e = expand_expr ctx e in
        ctx, {exp with expr = E_field (e, f)}
    | E_case (e, bs) ->
        (* Since [e] gets bound in the [clauses], we need to check
           for forbidden bindings. *)
        check_ho_binding exp;

        let ctx, e  = expand_expr ctx e in
        let ctx, bs =
          List.fold_left (fun (ctx, bs) (p, e) ->
              let ctx, e = expand_expr ctx e in
              ctx, (p, e) :: bs
            ) (ctx, []) bs in
        ctx, {exp with expr = E_case (e, List.rev bs)}
    | E_let (p, d, e) ->
        (* check let binding for forbidden expressions *)
        check_ho_binding d;

        let ctx, d = expand_expr ctx d in
        let ctx, e = expand_expr ctx e in
        ctx, {exp with expr = E_let (p, d, e)}
    | E_cast (e, t) ->
        let ctx, e = expand_expr ctx e in
        ctx, {exp with expr = E_cast (e, t)}
    | E_apply ({expr = E_mod_member (m, i);
                expr_loc = l; _}, es)
         when TypeAlgebra.is_higher_order (m, i) ->
        (* Rewrite this invocation after expanding its arguments *)
        let ctx, es = expand_exprs ctx es in
        expand_call ctx ((m, i, l), exp.expr_loc) es
    | E_apply (f, es) ->
        let ctx, f  = expand_expr ctx f in
        let ctx, es = expand_exprs ctx es in
        ctx, {exp with expr = E_apply (f, es)}

and expand_exprs ctx es : context * (unit, unit) expr list =
  let ctx, es =
    List.fold_left (fun (ctx, es) e ->
        let ctx, e = expand_expr ctx e in
        ctx, e :: es
      ) (ctx, []) es in
  ctx, List.rev es

(* traversals over other AST structures to scan and expand all
   embedded expressions *)

let rec expand_stmt ctx s : context * (unit, unit) stmt =
  match s.stmt with
    | S_assign (l, r) ->
        let ctx, l = expand_expr ctx l in
        let ctx, r = expand_expr ctx r in
        ctx, {s with stmt = S_assign (l, r)}
    | S_let (p, d, ss) ->
        (* Similar to E_let *)
        check_ho_binding d;

        let ctx, d = expand_expr ctx d in
        let ctx, ss = expand_stmts ctx ss in
        ctx, {s with stmt = S_let (p, d, ss)}
    | S_case (e, bs) ->
        (* Similar to E_case *)
        check_ho_binding e;

        let ctx, e = expand_expr ctx e in
        let ctx, bs =
          List.fold_left (fun (ctx, bs) (p, ss) ->
              let ctx, ss = expand_stmts ctx ss in
              ctx, (p, ss) :: bs
            ) (ctx, []) bs in
        ctx, {s with stmt = S_case (e, List.rev bs)}

and expand_stmts ctx ss : context * (unit, unit) stmt list =
  let ctx, ss =
    List.fold_left (fun (ctx, ss) s ->
        let ctx, s = expand_stmt ctx s in
        ctx, s :: ss
      ) (ctx, []) ss in
  ctx, List.rev ss

let expand_action ctx a =
  let ss, oe = a.action_stmts in
  let ctx, ss = expand_stmts ctx ss in
  let ctx, oe = match oe with
      | None   -> ctx, None
      | Some e -> let ctx, e = expand_expr ctx e in
                  ctx, Some e in
  ctx, {a with action_stmts = ss, oe}

let rec expand_regexp ctx re : context * (unit, unit) regexp =
  match re.regexp with
    | RX_empty | RX_literals _ | RX_wildcard | RX_type _ ->
        ctx, re
    | RX_star (re', oe) ->
        let ctx, re' = expand_regexp ctx re' in
        let ctx, oe = match oe with
            | None   -> ctx, None
            | Some e -> let ctx, e = expand_expr ctx e in
                        ctx, Some e in
        ctx, {re with regexp = RX_star (re', oe)}
    | RX_opt re' ->
        let ctx, re' = expand_regexp ctx re' in
        ctx, {re with regexp = RX_opt re'}
    | RX_choice res ->
        let ctx, res = expand_regexps ctx res in
        ctx, {re with regexp = RX_choice res}
    | RX_seq res ->
        let ctx, res = expand_regexps ctx res in
        ctx, {re with regexp = RX_seq res}

and expand_regexps ctx res =
  let ctx, res =
    List.fold_left (fun (ctx, res) re ->
        let ctx, re = expand_regexp ctx re in
        ctx, re :: res
      ) (ctx, []) res in
  ctx, List.rev res

let rec expand_rule_elem ctx re : context * (unit, unit) rule_elem =
  match re.rule_elem with
    | RE_bitvector _ | RE_align _ | RE_pad _ | RE_bitfield _ | RE_epsilon ->
        ctx, re
    | RE_regexp r ->
        let ctx, r = expand_regexp ctx r in
        ctx, {re with rule_elem = RE_regexp r}
    | RE_non_term (n, oa) ->
        let ctx, oa = match oa with
            | None    ->
                ctx, None
            | Some ias ->
                let ctx, ias =
                  List.fold_left (fun (ctx, ias) (i, e) ->
                      let ctx, e = expand_expr ctx e in
                      ctx, (i, e) :: ias
                    ) (ctx, []) ias in
                ctx, Some (List.rev ias) in
        ctx, {re with rule_elem = RE_non_term (n, oa)}
    | RE_named (n, re') ->
        let ctx, re' = expand_rule_elem ctx re' in
        ctx, {re with rule_elem = RE_named (n, re')}
    | RE_action a ->
        let ctx, a = expand_action ctx a in
        ctx, {re with rule_elem = RE_action a}
    | RE_constraint e ->
        let ctx, e = expand_expr ctx e in
        ctx, {re with rule_elem = RE_constraint e}
    | RE_seq res ->
        let ctx, res = expand_rule_elems ctx res in
        ctx, {re with rule_elem = RE_seq res}
    | RE_choice res ->
        let ctx, res = expand_rule_elems ctx res in
        ctx, {re with rule_elem = RE_choice res}
    | RE_star (re', oe) ->
        let ctx, re' = expand_rule_elem ctx re' in
        let ctx, oe = match oe with
            | None   -> ctx, None
            | Some e -> let ctx, e = expand_expr ctx e in
                        ctx, Some e in
        ctx, {re with rule_elem = RE_star (re', oe)}
    | RE_opt re' ->
        let ctx, re' = expand_rule_elem ctx re' in
        ctx, {re with rule_elem = RE_opt re'}
    | RE_set_view e ->
        let ctx, e = expand_expr ctx e in
        ctx, {re with rule_elem = RE_set_view e}
    | RE_at_pos (e, re') ->
        let ctx, e = expand_expr ctx e in
        let ctx, re' = expand_rule_elem ctx re' in
        ctx, {re with rule_elem = RE_at_pos (e, re')}
    | RE_at_view (e, re') ->
        let ctx, e = expand_expr ctx e in
        let ctx, re' = expand_rule_elem ctx re' in
        ctx, {re with rule_elem = RE_at_view (e, re')}
    | RE_map_views (e, re') ->
        let ctx, e = expand_expr ctx e in
        let ctx, re' = expand_rule_elem ctx re' in
        ctx, {re with rule_elem = RE_map_views (e, re')}
    | RE_seq_flat res ->
        let ctx, res = expand_rule_elems ctx res in
        ctx, {re with rule_elem = RE_seq_flat res}

and expand_rule_elems ctx res : context * (unit, unit) rule_elem list =
  let ctx, res =
    List.fold_left (fun (ctx, res) re ->
        let ctx, re = expand_rule_elem ctx re in
        ctx, re :: res
      ) (ctx, []) res in
  ctx, List.rev res

let expand_rule ctx r : context * (unit, unit) rule =
  let ctx, res = expand_rule_elems ctx r.rule_rhs in
  let ctx, tmps =
    List.fold_left (fun (ctx, ts) (v, te, e) ->
        let ctx, e = expand_expr ctx e in
        ctx, (v, te, e) :: ts
      ) (ctx, []) r.rule_temps in
  ctx, {r with rule_rhs   = res;
               rule_temps = List.rev tmps}

let expand_rules ctx rs : context * (unit, unit) rule list =
  let ctx, rs =
    List.fold_left (fun (ctx, rs) r ->
        let ctx, r = expand_rule ctx r in
        ctx, r :: rs
      ) (ctx, []) rs in
  ctx, List.rev rs

let expand_alt ctx alt =
  match alt with
    | ALT_type _ ->
        ctx, alt
    | ALT_decls ds ->
        let ctx, ds =
          List.fold_left (fun (ctx, ds) (i, t, oe) ->
              let ctx, oe = match oe with
                  | None   -> ctx, None
                  | Some e -> let ctx, e = expand_expr ctx e in
                              ctx, Some e in
              ctx, (i, t, oe) :: ds
            ) (ctx, []) ds in
        ctx, ALT_decls (List.rev ds)

let expand_non_term_defn ctx ntd : context * (unit, unit) non_term_defn =
  let ctx, alt = expand_alt ctx ntd.non_term_syn_attrs in
  let ctx, rs  = expand_rules ctx ntd.non_term_rules in
  ctx, {ntd with non_term_syn_attrs = alt;
                 non_term_rules = rs}

(* After we scan and expand the function body, register the
   definition in the context *)
let expand_func ctx f : context * (unit, unit) fun_defn =
  let ctx, b = expand_expr ctx f.fun_defn_body in
  let f = {f with fun_defn_body = b} in
  let fid = fst (Location.value f.fun_defn_ident) in
  let ctx_fdefs = StringMap.add fid f ctx.ctx_fdefs in
  {ctx with ctx_fdefs}, f

let expand_const ctx c : context * (unit, unit) const_defn =
  let ctx, e = expand_expr ctx c.const_defn_val in
  ctx, {c with const_defn_val = e}

let expand_format_decl ctx fd : context * (unit, unit) format_decl =
  let ctx, ntd = expand_non_term_defn ctx fd.format_decl in
  ctx, {fd with format_decl = ntd}

let expand_format_decls ctx fds : context * (unit, unit) format_decl list =
  let ctx, fds =
    List.fold_left (fun (ctx, fds) fd ->
        let ctx, fd = expand_format_decl ctx fd in
        ctx, fd :: fds
      ) (ctx, []) fds in
  ctx, List.rev fds

let expand_format ctx f : context * (unit, unit) format =
  let ctx, ds = expand_format_decls ctx f.format_decls in
  ctx, {f with format_decls = ds}

(* initialize context with builtins *)
let init_ctx () =
  let builtins =
    List.fold_left (fun acc m ->
        let MName mn = TypeAlgebra.(m.mod_name) in
        List.fold_left (fun acc ((DName dn, _, _) as d) ->
            StdlibMap.add (mn, dn) d acc
          ) acc TypeAlgebra.(m.mod_values)
      ) StdlibMap.empty TypeAlgebra.builtin_modules in
  {ctx_fdefs   = StringMap.empty;
   ctx_stddefs = builtins;
   ctx_synths  = [];
   ctx_cache   = SynthCache.empty}

let expand_spec (spec: (unit, unit) program)
    : (unit, unit) program =
  let ctx = init_ctx () in
    let splice ctx d ds =
    (* `ds` is in reverse order, and the synthesized functions
       in`ctx_synths` are in reverse order to their calls in the
       expanded component.  We need to ensure that the synthesized
       functions appear before the expanded component to ensure
       proper scoping. *)
    let ds =
      d :: ((List.map (fun f -> Decl_fun f) ctx.ctx_synths) @ ds) in
    {ctx with ctx_synths = []}, ds in

  let _, decls =
    List.fold_left (fun (ctx, ds) d ->
        (* ensure all synthesized functions have been incorporated *)
        assert (List.length ctx.ctx_synths = 0);
        match d with
          | Decl_types _ ->
              ctx, d :: ds
          | Decl_const c ->
              let ctx, c = expand_const ctx c in
              splice ctx (Decl_const c) ds
          | Decl_fun f ->
              (* We should never find a synthesized function as input *)
              assert (not f.fun_defn_synth);
              let ctx, f = expand_func ctx f in
              splice ctx (Decl_fun f) ds
          | Decl_format f ->
              let ctx, f = expand_format ctx f in
              splice ctx (Decl_format f) ds
      ) (ctx, []) spec.decls in
  {decls = List.rev decls}
