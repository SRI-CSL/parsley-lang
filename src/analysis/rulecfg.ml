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

(* An analysis to ensure that all synthesized attributes of a
   non-terminal are assigned in each of its production rules, and no
   uninitialized variables are used in any expression.  *)

open Parsing
open Ast
module TE = Typing.TypingEnvironment
open Typing.TypeInfer
open Typing.TypedAstUtils
open Flow
open Dataflow

type typ = Typing.MultiEquation.crterm

(* Attributes may have record types whose fields may also be a record.
   This leads to such an attribute possessing a tree structure of
   locations whose initialization status needs to be tracked.

   A binding is represented by the variable for the non-terminal and
   its associated tree-structure: the synthesized attributes are the
   immediate children of the variable, with the fields of any
   attribute with record type forming the children of the attribute,
   and recursively for any record fields with record type.

   The primary invariants for this structure are:
   . if a node with children is not directly initialized, it can be
     considered initialized if all its children are initialized.
   . if a node with children is directly initialized, the
     initialization states of the children are irrelevant.
 *)

(* A node in the field binding tree. *)
module BNode = struct
  module FieldMap = Map.Make(struct
                        type t = mname * string
                        let compare = AstUtils.qual_compare
                      end)

  type 'a node =
    {n_fname:    mname * string;
     n_children: 'a node FieldMap.t;
     n_aux:      'a option}

  (* Roots are not themselves fields, and are not module qualified;
     so just put them in the stdlib module. *)
  let new_root (name: string) =
    {n_fname    = AstUtils.stdlib, name;
     n_children = FieldMap.empty;
     n_aux      = None}

  (* This is only for internal use; should be hidden from clients. *)
  let new_node (fname: mname * string) =
    {n_fname    = fname;
     n_children = FieldMap.empty;
     n_aux      = None}

  let assert_nequal n n' =
    assert (AstUtils.qual_compare n n' = 0)

  let str_of_name (m, f) =
    Printf.sprintf "%s%s" (AstUtils.mk_modprefix m) f

  (* The field sequence `fs` denotes a path to a child node, with an
     empty sequence denoting the `root`. *)
  let find_node (type a) (root: a node) (fs: (mname * string) list)
      : a node option =
    let rec finder nd fs =
      match fs with
        | []      -> Some nd
        | f :: fs -> (match FieldMap.find_opt f nd.n_children with
                        | None    -> None
                        | Some nd -> (assert_nequal f nd.n_fname;
                                      finder nd fs)) in
    finder root fs

  (* Update the node info at the specified path and return the updated
     root, creating child nodes along the path if needed. *)
  let update_node (type a) (root: a node) (fs: (mname * string) list) aux
      : a node =
    let rec update nd fs =
      match fs with
        | [] ->
            {nd with n_aux = aux}
        | f :: fs ->
            let cd = match FieldMap.find_opt f nd.n_children with
                | None    -> new_node f
                | Some cd -> assert_nequal f cd.n_fname;
                             cd in
            let cd = update cd fs in
            {nd with n_children = FieldMap.add f cd nd.n_children} in
    update root fs

  (* A node is 'subtree-defined' if either it has a set `aux` value,
     or all of its children are 'subtree-defined'. *)
  let is_subtree_defined (type a) (nd: a node) : bool =
    let rec checker _fn nd =
      match nd.n_aux with
        | Some _ -> true
        | None   -> if   FieldMap.is_empty nd.n_children
                    then false
                    else FieldMap.for_all checker nd.n_children in
    checker nd.n_fname nd

  (* A node is 'defined' if any parent upto the root has a set `aux`
     value, or it is 'subtree-defined'. *)
  let is_defined (type a) (root: a node) (fs: (mname * string) list) : bool =
    let rec checker nd fs =
      if   nd.n_aux <> None
      then true
      else match fs with
             | []      -> is_subtree_defined nd
             | f :: fs -> (match FieldMap.find_opt f nd.n_children with
                             | None    -> false
                             | Some nd -> checker nd fs) in
    checker root fs

  (* Two nodes are equal if they have the same `aux` value, their
     children have the same names and are equal. *)
  let are_equal (type a) (l: a node) (r: a node) : bool =
    let rec eq (l, r) =
      l.n_aux = r.n_aux
      && (let lfs, lns = List.split (FieldMap.bindings l.n_children) in
          let rfs, rns = List.split (FieldMap.bindings r.n_children) in
          lfs = rfs
          && List.for_all eq (List.combine lns rns)) in
    eq (l, r)

  (* List of the elements in the tree rooted at the node.  This
     should only be called on the actual roots of a binding tree. *)
  let elements (type a) (root: a node)
      : ((mname * string) list * a option) list =
    let rec kids_of at_root nd =
      if   FieldMap.is_empty nd.n_children
      then [(if at_root then [] else [nd.n_fname]), nd.n_aux]
      else List.fold_left (fun acc (_, k) ->
               (List.rev_map (fun (fs, a) ->
                    (if at_root then fs else nd.n_fname :: fs), a
                  ) (kids_of false k)
               ) @ acc
             ) [] (FieldMap.bindings nd.n_children) in
    kids_of true root

  (* Merge two trees with the same root, using a join on their `aux`
     fields.  The join obeys `None < Some _` on each node, and the
     resulting tree contains a union of the nodes. *)
  let join (type a) (l: a node) (r: a node) : a node =
    let merge_aux = function None, a | a, None | a, _ -> a in
    let rec merge l r =
      assert_nequal l.n_fname r.n_fname;
      (* For each child `rk` of `r`, add it to `l` if the corresponding
         child `lk` is not present, or add `merge lk rk` to `l`
         otherwise. *)
      {l with
        n_children =
          FieldMap.fold (fun rkn rk lm ->
              match FieldMap.find_opt rkn lm with
                | None    -> FieldMap.add rkn rk lm
                | Some lk -> FieldMap.add rkn (merge lk rk) lm
            ) r.n_children l.n_children;
        n_aux = merge_aux (l.n_aux, r.n_aux)} in
    merge l r

  let print (type a) (n: a node) =
    let rec pr depth n =
      let set = match n.n_aux with
          | None   -> "?"
          | Some _ -> "!" in
      let fill = String.make (3 * depth + 3) ' ' in
      Printf.eprintf "%s%s%s @ depth %d\n" fill (str_of_name n.n_fname) set depth;
      Seq.iter (fun (_, k) ->
          pr (depth + 1) k
        ) (FieldMap.to_seq n.n_children) in
    pr 0 n
end

(* The state for a variable binding is represented by its unique
   identifier and the root node for an optional tree of fields.  Its
   name and location are tracked for error reporting purposes, but
   they are not used for comparisons.
 *)
type 'a var_info = varid * 'a BNode.node * (string * Location.t)

(* A reference to a variable or one of its possibly nested fields is
   similarly represented, except that if present, the fields form a
   simple sequence: i.e. `a.b.c` generates `[b; c]` with head variable
   `a`.
 *)
type reference = varid * (mname * string) list * (string * Location.t)

let rec compare_fields fs fs' =
  match fs, fs' with
    | [], []             ->  0
    | [], _::_           -> -1
    | _::_, []           ->  1
    | f :: fs, f' :: fs' -> let cf = AstUtils.qual_compare f f' in
                            if   cf = 0
                            then compare_fields fs fs'
                            else cf

(* reference comparisons ignore the debug information *)
let compare_reference (v, fs, _ig) (v', fs', _ig') =
  let cv = compare v v' in
  if   cv = 0
  then compare_fields fs fs'
  else cv

(* useful conversions *)
let field_to_string (m, f) =
  Printf.sprintf "%s%s" (AstUtils.mk_modprefix m) f

let reference_to_string ((id, fs, (n, _)): reference) =
  let is = varid_to_string id in
  match fs with
    | [] -> Printf.sprintf "%s[%s]" n is
    | _  -> Printf.sprintf "%s[%s].%s" n is
              (String.concat "." (List.map field_to_string fs))

type init_var_error =
  | Use_of_uninit_var of reference
  | Unnamed_attributed_nonterminal of ident
  | Unassigned_attribute of ident * (mname * string) list
  | Unassigned_variable  of ident * string

exception Error of Location.t * init_var_error

module References = struct
  module R = Set.Make(struct
                 type t = reference
                 let compare = compare_reference
               end)
  include R

  let print b =
    let es = List.map reference_to_string (elements b) in
    String.concat ", " es
end

let vars_of_pattern (p: (typ, varid, mod_qual) pattern) : References.t =
  let rec add set p =
    match p.pattern with
      | P_wildcard | P_literal _ ->
          set
      | P_var v ->
          let v  = Location.value v in
          let ig = fst v, p.pattern_loc in
          References.add (snd v, [], ig) set
      | P_variant (_, ps) ->
          List.fold_left add set ps in
  add References.empty p

(* If a `bound` variable set is provided, this computes the free
   variables (i.e. that are not in `bound`) of the expression.
 *)
let free_vars_of_expr (e: (typ, varid, mod_qual) expr) (bound: References.t)
    : References.t =
  let rec add ((set, bound) as acc) e =
    match e.expr with
      | E_var v ->
          let v' = Location.value v in
          let ig = fst v', Location.loc v in
          let id = snd v', [], ig in
          if   References.mem id bound
          then acc
          else References.add id set, bound
      | E_field (e', _) ->
          (match lhs_fields e with
             | None ->
                 add acc e'
             | Some (v, fs) ->
                 let ig = fst v, e.expr_loc in
                 let id = snd v, fs, ig in
                 if   References.mem id bound
                 then acc
                 else References.add id set, bound)
      | E_constr (_, es) ->
          List.fold_left add acc es
      | E_record fs ->
          List.fold_left (fun acc (_, e) -> add acc e) acc fs
      | E_apply (f, args) ->
          List.fold_left add (add acc f) args
      | E_case (e, cls) ->
          List.fold_left (fun (set, bound) (p, e) ->
              let bound = References.union bound (vars_of_pattern p) in
              add (set, bound) e
            ) (add acc e) cls
      | E_let (p, e', e) ->
          let set', bound' = add acc e' in
          let bound' = References.union bound' (vars_of_pattern p) in
          add (set', bound') e
      | E_binop (_, l, r) ->
          add (add acc l) r
      | E_recop (_, e) ->
          add acc e
      | E_bitrange (e, _, _) ->
          add acc e
      | E_literal _ | E_mod_member _ ->
          acc
      | E_unop (_, e) | E_match (e, _) | E_cast (e, _) ->
          add acc e in
  fst (add (References.empty, bound) e)

(* A node for the basic elements of the grammar language. *)
type gn =
  | GN_regexp
  | GN_type of ident
  | GN_constraint of (typ, varid, mod_qual) expr
  | GN_non_term of ident (* stripped of inherited attributes *)

let print_gn = function
  | GN_regexp ->
      "(gn: <regexp>)"
  | GN_type t ->
      Printf.sprintf "(gn: <type> %s)" (Location.value t)
  | GN_constraint _ ->
      Printf.sprintf "(gn: <constraint>)"
  | GN_non_term n ->
      Printf.sprintf "(gn: <non-term> %s)" (Location.value n)

type 'v gnode =
  {gnode:     gn;
   gnode_loc: Location.t;
   gnode_aux: 'v}

let print_gnode gn =
  print_gn gn.gnode

(* A node for basic non-branching expressions (including grammar
   constraints) and the assignment statement.
 *)
type en =
  | EN_expr of (typ, varid, mod_qual) expr
  | EN_defn of (typ, varid, mod_qual) pattern
  (* variable/record-field assignment *)
  | EN_binding_assign of References.elt * (typ, varid, mod_qual) expr
  (* other assignments *)
  | EN_assign of (typ, varid, mod_qual) expr * (typ, varid, mod_qual) expr

let print_en = function
  | EN_expr _           -> "(en: <expr>)"
  | EN_defn _           -> "(en: <defn>)"
  | EN_binding_assign _ -> "(en: <binding-assign>)"
  | EN_assign _         -> "(en: <assign>)"

type 'v enode =
  {enode:     en;
   enode_loc: Location.t;
   enode_aux: 'v}

let print_enode en =
  print_en en.enode

(* Dataflow node *)

module Node = struct
  type ('e, 'x, 'v) node =
    | N_enode: 'v enode         -> (Block.o, Block.o, 'v) node
    | N_gnode: 'v gnode         -> (Block.o, Block.o, 'v) node
    | N_label: Label.label      -> (Block.c, Block.o, 'v) node
    | N_jumps: Label.label list -> (Block.o, Block.c, 'v) node

  let entry_label (type x v) (n: (Block.c, x, v) node) =
    match n with
      | N_label l -> l
      (* this should not be needed *)
      | _ -> assert false

  let successors (type e v) (n: (e, Block.c, v) node) =
    match n with
      | N_jumps l -> l
      (* this should not be needed *)
      | _ -> assert false

  let print (type e x v) (n: (e, x, v) node) =
    match n with
      | N_gnode gn -> print_gnode gn
      | N_enode en -> print_enode en
      | N_label l  -> Printf.sprintf "(N: label %s)" (Label.to_string l)
      | N_jumps ls -> Printf.sprintf "(N: jumps %s)"
                        (String.concat ", " (List.map Label.to_string ls))

  let loc (type v) (n: (Block.o, Block.o, v) node) =
    match n with
      | N_gnode gn -> gn.gnode_loc
      | N_enode en -> en.enode_loc
      (* this should not be needed *)
      | _ -> assert false
end

(* The CFG *)

module G = Graph.MkGraph (Node)
module B = G.Block
module D = G.Body

(* The initialization state for a variable and any nested fields is
   the label of the block in which that variable or field was
   initialized.  This state is stored for every variable in a map
   indexed by the variable's varid.
 *)
module ReachingDefns = struct
  type var_state = Label.label var_info

  module VMap = Map.Make(struct
                    type t = varid
                    let compare = compare
                  end)
  type t = var_state VMap.t

  let empty = VMap.empty

  (* Checks whether a reference is being tracked. *)
  let has_reference ((vid, fs, _): reference) (rd: t) : bool =
    match fs, VMap.find_opt vid rd with
      | _, None               -> false
      | fs, Some (_, root, _) -> None <> BNode.find_node root fs

  (* List of references and their states. *)
  let elements (rd: t) : (reference * Label.label option) list =
    VMap.fold (fun vid (_, root, ig) acc ->
        List.rev_map
          (fun (fs, a) -> (vid, fs, ig), a)
          (BNode.elements root)
        @ acc
      ) rd []

  (* Register a variable or field binding. *)
  let add ((vid, fs, ig): reference) aux (rd: t) : t =
    let root, ig = match VMap.find_opt vid rd with
        | None                -> BNode.new_root (fst ig), ig
        | Some (_, root, ig') -> assert (fst ig = fst ig');
                                 root, ig' in
    let root = BNode.update_node root fs aux in
    VMap.add vid (vid, root, ig) rd

  (* Add or update initialization locations for references. *)
  let define (rs: References.t) (l: Label.label) (rd: t) : t =
    List.fold_left (fun rd r -> add r (Some l) rd)
      rd (References.elements rs)

  (* A reference is possibly undefined if it is undefined and none of
     its parents are. *)
  let possibly_undefined ((vid, fs, _): reference) (rd: t) : bool =
    match VMap.find_opt vid rd with
      | None              -> true
      | Some (_, root, _) -> not (BNode.is_defined root fs)

  (* Equal `ReachingDefns` have the entries for the same variables,
     with equal root binding nodes. *)
  let equal (l: t) (r: t) : bool =
    let lvs, lents = List.split (VMap.bindings l) in
    let rvs, rents = List.split (VMap.bindings r) in
    lvs = rvs && List.for_all (fun ((lid, lrt, _), (rid, rrt, _)) ->
                     assert (lid = rid);
                     BNode.are_equal lrt rrt
                   ) (List.combine lents rents)

  (* The union implements the lattice join on each variable and its
     fields. *)
  let union (l: t) (r: t) =
    (* For each entry `re` in `r`, add it to `l` if the corresponding
       entry `le` is not present, or merge the roots of `le` and `re`
       and add the merged entry to `l`. *)
    VMap.fold (fun rvid ((_, rroot, rig) as re) lm ->
        match VMap.find_opt rvid lm with
          | None ->
              VMap.add rvid re lm
          | Some (lvid, lroot, lig) ->
              assert (lvid = rvid);
              assert (fst lig = fst rig);
              let le = lvid, BNode.join lroot rroot, lig in
              VMap.add lvid le lm
      ) r l

  (* Debug printer *)
  let print (t: t) =
    Seq.iter (fun (_, (_, root, ig)) ->
        Printf.eprintf "%s:\n" (fst ig);
        BNode.print root;
      ) (VMap.to_seq t)
end

(* The lattice for the reaching definitions analysis. *)
module IVLattice = struct
  type t = ReachingDefns.t

  let bottom = ReachingDefns.empty

  let join a b =
    if   ReachingDefns.equal a b
    then NoChange, a
    else SomeChange, ReachingDefns.union a b

  let print rd =
    let print (b, ol) =
      Printf.sprintf "%s@%s"
        (reference_to_string b)
        (match ol with
           | Some l -> Label.to_string l
           | None   -> "?") in
    let es = List.map print (ReachingDefns.elements rd) in
    String.concat ", " es
end

(* Each node stores the bindings used and defined by it. *)
type v =
  {node_use: References.t;
   node_def: References.t * Label.label}

let print_v v =
  Printf.sprintf "[use: %s] [def: %s]"
    (References.print v.node_use) (References.print (fst v.node_def))

type opened = (Block.c, Block.o, v) B.block
type closed = (Block.c, Block.c, v) B.block

(* node construction and block extension *)

let add_expr (env: References.t) (b: opened) (e: (typ, varid, mod_qual) expr) =
  let l = B.entry_label b in
  let u = free_vars_of_expr e env in
  let v = {node_use = u; node_def = References.empty, l} in
  let n = {enode = EN_expr e; enode_loc = e.expr_loc; enode_aux = v} in
  (* Printf.eprintf "\t%s adding expr %s: %s\n"
    (Label.to_string l) (Node.print (N_enode n)) print_v v); *)
  B.snoc b (N_enode n)

let add_pattern (_: References.t) (b: opened) (p: (typ, varid, mod_qual) pattern) =
  (* Pattern matching binds and initializes its variables. *)
  let l = B.entry_label b in
  let d = vars_of_pattern p in
  let v = {node_use = References.empty; node_def = d, l} in
  let n = {enode = EN_defn p; enode_loc = p.pattern_loc; enode_aux = v} in
  (*Printf.eprintf "\t%s adding pattern %s: %s\n"
    (Label.to_string l) (Node.print (N_enode n)) print_v v);*)
  B.snoc b (N_enode n)

let add_binding_assign (env: References.t) (b: opened) a e =
  let l = B.entry_label b in
  let u = free_vars_of_expr e env in
  let d = References.singleton a in
  let v = {node_use = u; node_def = d, l} in
  let n = {enode     = EN_binding_assign (a, e);
           enode_loc = e.expr_loc;
           enode_aux = v} in
  (*Printf.eprintf "\t%s adding binding assignment %s: %s\n"
   (Label.to_string l) (Node.print (N_enode n)) (print_v v);*)
  B.snoc b (N_enode n)

(* TODO: does this ever get used in practise?  It leaves a potential
   hole in the analysis since the defs will not get counted. *)
let add_assign (env: References.t) (b: opened) a e =
  let l = B.entry_label b in
  (* The lhs is a general expr, so use an empty def. *)
  let u = free_vars_of_expr e env in
  let v = {node_use = u; node_def = References.empty, l} in
  let n = {enode     = EN_assign (a, e);
           enode_loc = e.expr_loc;
           enode_aux = v} in
  (*Printf.eprintf "\t%s adding assignment %s: %s\n"
   (Label.to_string l) (Node.print (N_enode n)) (print_v v);*)
  B.snoc b (N_enode n)

(* block construction *)

let new_labeled_block (l: Label.label) : opened =
  let h = Node.N_label l in
  (*Printf.eprintf "\tStarting new labeled block: %s\n" (Node.print h);*)
 B.join_head h B.empty

let new_block () : Label.label * opened =
  let l = Label.fresh_label () in
  l, new_labeled_block l

let end_block (b: opened) (l: Label.label list) : closed =
  let t = Node.N_jumps l in
  (*Printf.eprintf "\tEnding block with: %s\n" (Node.print t);*)
  B.join_tail b t

(* The context for generating the CFG is:
   . an environment containing some constant bound variables
     (e.g. from the standard library), which are excluded from the use
     sets for efficiency.
   . the accumulated set of closed blocks generated so far
   . the current open block into which the next node should be added
 *)
type ctx = References.t * closed list * opened

let rec add_stmt (ctx: ctx) (s: (typ, varid, mod_qual) stmt) : ctx =
  let bound, closed, b = ctx in
  match s.stmt with
    | S_assign ({expr = E_var v; _}, e) ->
        let ig = fst (Location.value v), Location.loc v in
        let l = snd (Location.value v), [], ig in
        let b = add_binding_assign bound b l e in
        bound, closed, b
    | S_assign (({expr = E_field _; _} as l), e) ->
        (match lhs_fields l with
           | None ->
               let b = add_assign bound b l e in
               bound, closed, b
           | Some (v, fs) ->
               let ig = fst v, s.stmt_loc in
               let l  = snd v, fs, ig in
               let b  = add_binding_assign bound b l e in
               bound, closed, b)
    | S_assign (l, e) ->
        let b = add_assign bound b l e in
        bound, closed, b
    | S_let (p, e, stmts) ->
        let b = add_expr bound b e in
        let b = add_pattern bound b p in
        List.fold_left add_stmt (bound, closed, b) stmts
    | S_case (e, cls) ->
        let b = add_expr bound b e in
        (* `b` will be closed below with the labels for the new blocks
           for the clauses.  Each of those blocks will need to jump
           to a new continuation block. *)
        let cl, cb = new_block () in
        let lbls, closed =
          List.fold_left (fun (lbls, closed) (p, ss) ->
              let l, b = new_block () in
              let b = add_pattern bound b p in
              let _, closed, b =
                List.fold_left add_stmt (bound, closed, b) ss in
              let c = end_block b [cl] in
              (l :: lbls), c :: closed
            ) ([], closed) cls in
        let c = end_block b lbls in
        bound, c :: closed, cb
    | S_print (_, e) ->
        let b = add_expr bound b e in
        bound, closed, b

let add_gnode (b: opened) gn loc =
  let l = B.entry_label b in
  let v = {node_use = References.empty; node_def = References.empty, l} in
  let g = {gnode = gn; gnode_loc = loc; gnode_aux = v} in
  (* Printf.eprintf "\t%s adding gnode %s\n" (Label.to_string l) (Node.print (N_gnode g));*)
  B.snoc b (N_gnode g)

(* Regular expressions use similar combinators as the production rules
   for attributed non-terminals; they are separated out in the AST for
   convenience in the typing rules, and they will likely also help in
   code generation.  For control-flow convenience however, we express
   the regexp combinators in terms of the combinators for the
   attributed rule elements.  We leave only the primitive regexps:
   literals and wildcards.
 *)
let rec lift_regexp rx =
  let wrap r =
    {rule_elem     = r;
     rule_elem_mod = rx.regexp_mod;
     rule_elem_loc = rx.regexp_loc;
     rule_elem_aux = rx.regexp_aux} in
  match rx.regexp with
    | RX_empty | RX_literals _ | RX_wildcard ->
        wrap (RE_regexp rx)
    | RX_type (m, id) ->
        wrap (RE_non_term (m, id, None))
    | RX_star (re', oe) ->
        let r' = lift_regexp re' in
        wrap (RE_star (r', oe))
    | RX_opt rx' ->
        wrap (RE_opt (lift_regexp rx'))
    | RX_choice rxs ->
        wrap (RE_choice (List.map lift_regexp rxs))
    | RX_seq rxs ->
        wrap (RE_seq_flat (List.map lift_regexp rxs))

(* The control flow semantics during parsing require that all
   assignment side-effects performed after a choice point along an
   execution path for a production rule are undone or rewound when a
   parse failure rewinds execution back to that choice point.  From
   the point of view of the initialization analysis, this is
   equivalent to a control-flow that does not have any failure paths.
   In other words, we need to ensure that all *purely* successful
   paths for a production rule end with all uninitialized attributes
   being initialized.
 *)

let pattern_of_var v loc aux : (typ, varid, mod_qual) pattern =
  {pattern     = P_var v;
   pattern_loc = loc;
   pattern_aux = aux}

let rec add_rule_elem
          (tenv: TE.environment)
          (ctx: ctx)
          (r: (typ, varid, mod_qual) rule_elem)
        : ctx =
  let env, closed, b = ctx in
  let pack b =
    env, closed, b in
  let mk_bitvector_ident () =
    Location.mk_loc_val "bitvector" r.rule_elem_loc in
  match r.rule_elem with
    | RE_regexp {regexp = RX_literals _; _}
    | RE_regexp {regexp = RX_wildcard; _} ->
        pack (add_gnode b GN_regexp r.rule_elem_loc)
    | RE_regexp rx ->
        let r' = lift_regexp rx in
        add_rule_elem tenv ctx r'
    | RE_non_term (_, id, oias) ->
        let b = match oias with
            | None     -> b
            | Some ias ->
                List.fold_left (fun b (_, _, e) ->
                    add_expr env b e
                  ) b ias in
        pack (add_gnode b (GN_type id) r.rule_elem_loc)
    (* Bitvectors and bitfields are treated just as types. *)
    | RE_bitvector _ ->
        let bv = mk_bitvector_ident () in
        pack (add_gnode b (GN_type bv) r.rule_elem_loc)
    | RE_bitfield t ->
        pack (add_gnode b (GN_type t) r.rule_elem_loc)
    | RE_constraint e
    | RE_set_view e ->
        pack (add_expr env b e)
    | RE_action {action_stmts = ss, oe; _}->
        let env, closed, b = List.fold_left add_stmt ctx ss in
        let b = match oe with
            | None   -> b
            | Some e -> add_expr env b e in
        env, closed, b
    | RE_named (n, r') ->
        (* `n` will only be defined after `r'` executes *)
        let env, closed, b = add_rule_elem tenv ctx r' in
        let p = pattern_of_var n r.rule_elem_loc r.rule_elem_aux in
        let b = add_pattern env b p in
        env, closed, b
    | RE_seq rs | RE_seq_flat rs ->
        List.fold_left (fun ctx r -> add_rule_elem tenv ctx r) ctx rs
    | RE_choice rs ->
        (* This introduces a branch point, so we need to terminate
           this block with jumps to each of the blocks that start the
           choices `rs`.  All the choices need a common continuation,
           so allocate a block for it. *)
        let cl, cb = new_block () in
        let ls, closed, env =
          List.fold_left (fun (ls, closed, env) r ->
              (* Allocate a new block to start this choice. *)
              let l, b = new_block () in
              let ctx = env, closed, b in
              let env, closed, b = add_rule_elem tenv ctx r in
              (* Jump to the common continuation. *)
              let c = end_block b [cl] in
              l :: ls, c :: closed, env
            ) ([], closed, env) rs in
        (* Terminate the current block with a jump to the choices. *)
        let c = end_block b ls in
        (* Resume from the common continuation. *)
        env, c :: closed, cb
    | RE_star (r', Some e) when is_non_zero e ->
        (* The count `e` is evaluated before `r'` is matched. For
           non-zero bounds, we have straight line execution. *)
        let b   = add_expr env b e in
        let ctx = env, closed, b in
        add_rule_elem tenv ctx r'
    | RE_star (r', Some e)
    | RE_map_views (e, r') ->
        (* If we can't statically determine that `e` is always
           non-zero for `RE_star` or non-empty for `RE_map_views`, we
           conservatively assume that they could be zero or empty, and
           create a branch point for the case that `r'` may not
           execute. *)
        let b = add_expr env b e in
        (* The below logic is similar to the `RE_star (r', None)` case. *)
        let cl, cb = new_block () in
        let bl, bb = new_block () in
        (* End the current block with these two as possible
           continuations. *)
        let c = end_block b [bl; cl] in
        let ctx = env, c :: closed, bb in
        let env, closed, bb = add_rule_elem tenv ctx r' in
        (* Insert a jump to the continuation. *)
        let c = end_block bb [cl] in
        env, c :: closed, cb
    | RE_star (r', None)
    | RE_opt r' ->
        (* These both create a branch point, since `r'` may not
           execute, and we could continue with the subsequent rule
           element.  Allocate a block for that continuation, and for
           `r'`. *)
        let cl, cb = new_block () in
        let bl, bb = new_block () in
        (* End the current block with these two as possible
           continuations. *)
        let c = end_block b [bl; cl] in
        let ctx = env, c :: closed, bb in
        let env, closed, bb = add_rule_elem tenv ctx r' in
        (* Insert a jump to the continuation. *)
        let c = end_block bb [cl] in
        env, c :: closed, cb
    | RE_epsilon
    | RE_align _
    | RE_pad _
    | RE_scan _ ->
        (* These are nops. *)
        ctx
    | RE_at_pos (e, r') | RE_at_view (e, r') ->
        (* `e` is evaluated before `r'` is matched. *)
        let b = add_expr env b e in
        let ctx = env, closed, b in
        add_rule_elem tenv ctx r'

(* A CFG for a production rule, and its final exit label. *)
let rule_to_cfg
      (tenv: TE.environment)
      (env: References.t)
      (m: mname)
      (ntd: (typ, varid, mod_qual) non_term_defn)
      (r: (typ, varid, mod_qual) rule)
    : Label.label * (Block.c, Block.c, v) G.graph * Label.label =
  (* Lookup type info for the non-terminal. *)
  let ntnm = Location.value ntd.non_term_name in
  let nti, _, _ = match TE.lookup_non_term tenv (m, (NName ntnm)) with
      | Some t -> t
      | None   -> assert false in
  (* The CFG needs an entry label and block to contain the setup for
     the rule, viz. the binding for the non-terminal itself
     (if present), and the attribute bindings and temporaries.  *)
  let entry_lbl, b = new_block () in
  (* Add inherited attributes. *)
  let b = List.fold_left (fun b (ia, _, _) ->
              let ian, _ = Location.value ia in
              let iloc   = Location.loc ia in
              (* We could loop over `nti` itself instead of looking
                 up, but doing it this way enables an extra asserted
                 consistency check.  *)
              let iat =
                match Typing.Misc.StringMap.find_opt ian (fst nti) with
                  | None        -> assert false
                  | Some (t, _) -> t in
              let p = pattern_of_var ia iloc iat in
              add_pattern env b p
            ) b ntd.non_term_inh_attrs in
  (* Add any initialized synthesized attributes. *)
  let b = match ntd.non_term_syn_attrs with
      | ALT_type _ -> b
      | ALT_decls ds when List.length ds = 0 -> b
      | ALT_decls ds ->
          let v =
            (match ntd.non_term_varname with
               | None ->
                   (* We could assert here, since this should have
                      been checked before we got here. *)
                   let loc = Location.loc ntd.non_term_name in
                   let err =
                     Unnamed_attributed_nonterminal ntd.non_term_name in
                   raise (Error (loc, err))
               | Some v -> v) in
          let v  = Location.value v in
          let vn = fst v in
          let v  = snd v in
          let m  = AstUtils.infer_mod ntd.non_term_mod in
          List.fold_left (fun b (f, _, _, oe) ->
              match oe with
                | None   -> b
                | Some e ->
                    let l =
                      let ig = vn, Location.loc f in
                      v, [m, Location.value f], ig in
                    add_binding_assign env b l e
            ) b ds in
  (* Add rule temporaries. *)
  let b = List.fold_left (fun b (tv, _, te) ->
              let loc = Location.loc tv in
              let p = pattern_of_var tv loc te.expr_aux in
              add_pattern env b p
            ) b r.rule_temps in
  let ctx = env, [], b in   (* the initial context *)
  (* Add the rule elements. *)
  let _, closed, b =
    List.fold_left (add_rule_elem tenv) ctx r.rule_rhs in
  (* Terminate the last block with a jump to an exit label. *)
  let exit_lbl = Label.fresh_label () in
  let c = end_block b [exit_lbl] in
  (* Construct the graph body, *)
  let body = List.fold_left D.add_block D.empty (c :: closed) in
  (* and the graph itself. *)
  let g = G.from_body body in
  (* Return the graph, and the entry/exit labels. *)
  entry_lbl, g, exit_lbl

module FB = MkFactBase (IVLattice)
module VA = MkAnalysis (G) (FB)

let print_fbase fb =
  Label.LabelMap.iter (fun l b ->
      Printf.eprintf "  fact@%s: %s\n"
        (Label.to_string l) (IVLattice.print b)
    ) fb
(* node transfer functions *)

let tr_co (type v)
      (n: (Block.c, Block.o, v) B.node)
      (fb: Block.c VA.facts)
    : Block.o VA.facts =
  match n, fb with
    | N_label l, Facts_closed fb ->
        (* For this analysis, entry labels should always be present in
         * the factbase. *)
        (match FB.lookup fb l with
           | Some f -> Facts_open f
           | None   -> assert false)
    | _ ->
        (* this should not be needed *)
        assert false

let tr_oc (type v)
      (n: (Block.o, Block.c, v) B.node)
      (f: Block.o VA.facts)
    : Block.c VA.facts =
  match n, f with
    | N_jumps js, Facts_open f ->
        let facts = List.map (fun j -> (j, f)) js in
        Facts_closed (FB.mk_factbase facts)
    | _, _ ->
        (* this should not be needed *)
        assert false

let tr_oo
      (n: (Block.o, Block.o, v) B.node)
      (f: Block.o VA.facts)
    : Block.o VA.facts =
  let check_use (inits: ReachingDefns.t) (uses: References.t) loc =
    (* All `u` in `uses` should be in the initialized set `inits`. *)
    References.iter (fun b ->
        if   ReachingDefns.possibly_undefined b inits
        then raise (Error (loc, Use_of_uninit_var b))
      ) uses in
  (* Add defs to outgoing set of initvars after checking uses. *)
  match f with
    | Facts_open f ->
        let out = match n with
            | N_enode e ->
                let use    = e.enode_aux.node_use in
                let def, l = e.enode_aux.node_def in
                check_use f use e.enode_loc;
                ReachingDefns.define def l f
            | N_gnode g ->
                let use    = g.gnode_aux.node_use in
                let def, l = g.gnode_aux.node_def in
                check_use f use g.gnode_loc;
                ReachingDefns.define def l f
            | _ ->
                (* this should not be needed *)
                assert false in
        (*Printf.eprintf
          " transfer: @node %s: {%s} -> {%s}\n"
          (Node.print n) (IVLattice.print f) (IVLattice.print out);*)
        Facts_open out

    | Facts_closed _ ->
        assert false

let fwd_transfer : v VA.fwd_transfer =
  (tr_co, tr_oo, tr_oc)

(* Build up the base set of initialized variables:
   . constants and functions from the prelude
   . constants and functions defined in the spec
 *)
let build_init_bindings (init_venv: VEnv.t) (tspec: (typ, varid) spec_module) =
  let mk_elem v =
    let loc = Location.loc v in
    let n, vid = Location.value v in
    vid, [], (n, loc) in
  let init = VEnv.fold_left (fun init v ->
                 References.add (mk_elem v) init
               ) References.empty init_venv in
  List.fold_left (fun init d ->
      match d with
        | Decl_types _ | Decl_format _ ->
            init
        | Decl_const c ->
            References.add (mk_elem c.const_defn_ident) init
        | Decl_fun f ->
            References.add (mk_elem f.fun_defn_ident) init
        | Decl_recfuns r ->
            List.fold_left (fun e f ->
                References.add (mk_elem f.fun_defn_ident) e
              ) init r.recfuns
    ) init tspec.decls

(* To build a complete list of all the nested field references of an
   attribute, all nested record types need to be traversed.  Some
   helpers for this are first defined. *)

(* A helper to extract the record info for the synthesized attributes
   of a non-terminal. *)
let get_nt_recinfo (tenv: TE.environment) mname (nt: string)
    : TE.record_info option =
  match TE.lookup_non_term tenv (mname, (NName nt)) with
    | Some (_, _, nts) ->
        (match nts with
           | NTT_type (_, r)   -> r
           | NTT_record (_, r) -> !r)
    | None -> None

(* Helpers to check if a type is a record, and if so, to
   extract the fields and their types. *)
let recinfo_of_type (tenv: TE.environment) (m: mname) (t: tvar)
    : (mname * (string * type_expr) list) option =
  match TE.get_record_info tenv (m, (TName (Location.value t))) with
    | None    -> None
    | Some ri -> let m = TE.(ri.modul) in
                 Some (m, List.map (fun (f, t) -> Location.value f, t) ri.fields)
let recinfo_of_type_expr (tenv: TE.environment) (t: type_expr)
    : (mname * (string * type_expr) list) option =
  match t.type_expr with
    | TE_tname (m, t)
    | TE_tapp ({type_expr = TE_tname (m, t);_}, _) ->
        recinfo_of_type tenv m t
    | TE_tvar _ | TE_tapp _ ->
        None
(* The builder of the complete list. *)
let build_attribute_refs (tenv: TE.environment) recinfo =
  let rec builder (m: mname) (f: string) (t: type_expr)
          : (mname * string) list list =
    match recinfo_of_type_expr tenv t with
      | None ->
          [[m, f]]
      | Some (m', fts) ->
          List.fold_left (fun acc (f', t) ->
              (List.rev_map (fun fs -> (m, f) :: fs) (builder m' f' t))
              @ acc
            ) [] fts in
  List.fold_left (fun acc (f, t) ->
      (builder TE.(recinfo.modul) (Location.value f) t)
      @ acc
    ) [] TE.(recinfo.fields)

let test_attr_builder tenv recinfo =
  let refs = build_attribute_refs tenv recinfo in
  let pr fs = Printf.eprintf " %s\n"
                (String.concat "." (List.map field_to_string fs)) in
  Printf.eprintf " built the following full refs:\n";
  List.iter pr refs

(** Check whether an attribute or record field is initialized. *)

(* Check the rules for a non-terminal. *)
let check_non_term (tenv: TE.environment) (init_env: References.t) ntd =
  (*  Printf.eprintf "checking %s:\n" (Location.value ntd.non_term_name);*)

  (* lookups default to the current module *)
  let mname = AstUtils.infer_mod ntd.non_term_mod in

  (* Set up the initial factbase: at the entry label, we only have
     uninitialized synthesized attributes, and no initialized
     variables (since we've pruned all entries from the prelude when
     constructing the CFG). *)
  let syn_attrs =
    let ntnm = Location.value ntd.non_term_name in
    let recinfo = get_nt_recinfo tenv mname ntnm in
    match recinfo, ntd.non_term_varname with
      | None, None ->
          None
      | None, Some v ->
          Some (v, [])
      | Some _, None ->
          (* Initialized attributes are best modeled as assignments in
             which the lhs is a field indexed variable.  If the
             non-terminal is not named, this is not possible; and any
             non-initialized attributes cannot be assigned.  For
             simplicity, just require that a non-terminal with
             synthesized attributes must use a local name. *)
          let loc = Location.loc ntd.non_term_name in
          let err =
            Unnamed_attributed_nonterminal ntd.non_term_name in
          raise (Error (loc, err))
      | Some ri, Some v ->
          Some (v, build_attribute_refs tenv ri) in
  let reaching_defs =
    match syn_attrs with
      | None ->
          ReachingDefns.empty
      | Some (v, []) ->
          (* Create an undefined binding for the variable. *)
          let lc = Location.loc v in
          let vn = fst (Location.value v) in
          let v  = snd (Location.value v) in
          let b  = v, [], (vn, lc) in
          ReachingDefns.add b None ReachingDefns.empty
      | Some (v, lfs) ->
          (* Create undefined bindings for each attribute. *)
          List.fold_left (fun rd fs ->
              let lc = Location.loc v in
              let vn = fst (Location.value v) in
              let v  = snd (Location.value v) in
              let b  = v, fs, (vn, lc) in
              ReachingDefns.add b None rd
            ) ReachingDefns.empty lfs in
  let rn = ref 0 in
  List.iter (fun r ->
      (*Printf.eprintf "  building cfg for rule %d:\n" !rn;*)
      (* Compute the CFG for the rule. *)
      let entry, cfg, exit = rule_to_cfg tenv init_env mname ntd r in
      (*Printf.eprintf
        "  built cfg for rule %d with entry %s and exit %s\n"
        !rn (Label.to_string entry) (Label.to_string exit);*)
      incr rn;
      let init_fbase =
        FB.mk_factbase [entry, reaching_defs] in
      (*Printf.eprintf "init_fbase:\n";
      print_fbase init_fbase;*)
      let init_fbase = VA.Facts_closed init_fbase in

      (* Call the forward analysis to get final factbase at `exit`. *)
      let exit_fbase, _opt_factmap =
        VA.fwd_analysis init_fbase (JustC [entry]) cfg fwd_transfer in
      (* Collect info on assignments of synthesized attributes. *)
      match syn_attrs with
        | None ->
            ()
        | Some (v, []) ->
            let loc = Location.loc v in
            let vn  = fst (Location.value v) in
            let v   = snd (Location.value v) in
            let exit_fbase = match exit_fbase with
                | VA.Facts_closed fb -> fb
                | VA.Facts_open _ -> assert false in
            (*Printf.eprintf "exit_fbase:\n";
            print_fbase exit_fbase;*)
            let exit_fact = match FB.lookup exit_fbase exit with
                | None -> assert false
                | Some f -> f in
            let b = v, [], (vn, loc) in
            if   ReachingDefns.possibly_undefined b exit_fact
            then let err =
                   Unassigned_variable (ntd.non_term_name, vn) in
                 raise (Error (r.rule_loc, err))
        | Some (v, lfs) ->
            let loc = Location.loc v in
            let vn  = fst (Location.value v) in
            let v   = snd (Location.value v) in
            let exit_fbase = match exit_fbase with
                | VA.Facts_closed fb -> fb
                | VA.Facts_open _ -> assert false in
            (*Printf.eprintf "exit_fbase:\n";
            print_fbase exit_fbase;*)
            let exit_fact = match FB.lookup exit_fbase exit with
                | None -> assert false
                | Some f -> f in
            (*Printf.eprintf "exit_reaching_defs:\n";
            ReachingDefns.print exit_fact;*)
            (* Ensure all synthesized attributes are initialized at exit. *)
            List.iter (fun fs ->
                let attr = v, fs, (vn, loc) in
                (*Printf.eprintf " init-check for %s@%s:\n"
                  (reference_to_string attr) (Label.to_string exit);*)
                if   ReachingDefns.possibly_undefined attr exit_fact
                then let err =
                       Unassigned_attribute (ntd.non_term_name, fs) in
                     raise (Error (r.rule_loc, err))
              ) lfs
    ) ntd.non_term_rules

(* entry into this module *)
let check_spec init_envs (tenv: TE.environment) (tspec: (typ, varid) spec_module) =
  let _, init_venv = init_envs in
  let init = build_init_bindings init_venv tspec in
  List.iter (fun d ->
      match d with
        | Decl_types _ | Decl_fun _ | Decl_recfuns _ | Decl_const _ -> ()
        | Decl_format f ->
            List.iter (fun fd ->
                check_non_term tenv init fd.format_decl
              ) f.format_decls
    ) tspec.decls

(* error messages *)

let error_msg =
  (* strip module qualifiers for readability *)
  let strip_mods fs = List.map (fun (_, f) -> f) fs in
  function
  | Use_of_uninit_var ((_v, fs, (n, _))) ->
      let fs = strip_mods fs in
      Printf.sprintf "`%s' may be used uninitialized."
        (match fs with
           | [] -> n
           | _  -> Printf.sprintf "%s.%s" n (String.concat "." fs))
  | Unnamed_attributed_nonterminal nt ->
      Printf.sprintf "Non-terminal `%s' with synthetic attributes needs to be  given a local name."
        (Location.value nt)
  | Unassigned_attribute (nt, fs) ->
      Printf.sprintf "Attribute `%s' of `%s' may be uninitialized at the end of this rule."
        (String.concat "." (strip_mods fs)) (Location.value nt)
  | Unassigned_variable (nt, v) ->
      Printf.sprintf "Variable `%s' of `%s' may be uninitialized at the end of this rule."
        v (Location.value nt)
