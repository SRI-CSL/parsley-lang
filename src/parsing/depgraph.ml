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

module type DepGraph = sig
    type node
    type t

    type cycle = node list

    val init:      t
    val add_deps:  t -> node -> node list -> (t, cycle) result
    val deps:      t -> node -> node list option
    val topo_sort: t -> (node list, cycle) result
end

module Make (Ord: Set.OrderedType) = struct
  module M = Map.Make(Ord)
  module S = Set.Make(Ord)

  type node = Ord.t

  (* The depgraph consists of the graph along with a root node, which
     is the first node whose deps are added to the graph. *)
  type t    = S.t M.t * node option

  type cycle = node list

  let init = M.empty, None

  let add_node ((g, root): t) (n: node) : t =
    let root = match root with
        | None   -> Some n
        | Some _ -> root in
    match M.find_opt n g with
      | Some _ -> g, root
      | None   -> M.add n S.empty g, root

  let add_deps (g: t) (n: node) (ds: node list) : (t, cycle) result =
    let g, root = add_node g n in
    (* check for self-cycles *)
    let cycle =
      List.fold_left (fun c d ->
          match c with
            | Some _ -> c
            | None   -> if   Ord.compare n d = 0
                        then Some [n]
                        else None
        ) None ds in
    match cycle with
      | Some c -> Error c
      | None   -> Ok (M.add n (S.of_list ds) g, root)

  let deps ((g, _): t) (n: node) : node list option =
    match M.find_opt n g with
      | Some s -> Some (S.elements s)
      | None   -> None

  (* incremental depth first traversal from node `n`, at a path from
     the root specified by the node stack `stkl` (as a list, with
     `stks` as a set), accumulating its result into `result`. *)
  let rec traverse g (stks, stkl) result n =
    match result with
      | Error _ ->
          result
      | Ok (dones, _) ->
          let stkl = n :: stkl in
          if      S.mem n stks
          then    Error (List.rev stkl)
          else if S.mem n dones (* join point *)
          then    result
          else    let stks = S.add n stks in
                  let kids =
                    match M.find_opt n g with
                      | Some t -> S.elements t
                      | None   -> [] in
                  let result =
                    List.fold_left (traverse g (stks, stkl))
                      result kids in
                  match result with
                    | Error _ ->
                        result
                    | Ok (dones, deps) ->
                        let dones = S.add n dones in
                        (* deps are in parent (depender) first order *)
                        let deps  = n :: deps in
                        Ok (dones, deps)

  let topo_sort ((g, root): t) : (node list, cycle) result =
    match root with
      | None   -> Ok []
      | Some r -> let init = Ok (S.empty, []) in
                  let stk  = S.empty, [] in
                  match traverse g stk init r with
                    | Error c      -> Error c
                    (* return child (dependency) first order *)
                    | Ok (_, deps) -> Ok (List.rev deps)
end
