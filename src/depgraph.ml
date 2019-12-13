module type OrderedType = sig
    type t
    val compare: t -> t -> int
end

module type GraphType = sig
    type node
    type t

    exception Cycle of node list
    exception Node_not_present of node

    val init: t
    val add_link: t -> node -> node -> t
    val targets: t -> node -> node list
    val topo_sort: t -> node list
end

module Make (Ord : OrderedType) = struct
  type node = Ord.t
  type t = Set.Make(Ord).t Map.Make(Ord).t

  exception Node_not_present of node
  exception Cycle of node list

  module M = Map.Make(Ord)
  module S = Set.Make(Ord)

  let init = M.empty

  let add_node g n =
    match M.find_opt n g with
      | Some _ -> g
      | None -> M.add n S.empty g

  let add_link g n t =
    let g = add_node (add_node g n) t in
    let s = M.find n g in
    let s = S.add t s in
    M.add n s g

  let targets g n =
    match M.find_opt n g with
      | Some s -> S.elements s
      | None -> raise (Node_not_present n)

  (* not the most efficient, but purely functional *)
  let topo_sort g =
    let rec traverse tmps tmpl (dones, sorted) n =
      let tmpl = n :: tmpl in
      if S.mem n tmps
      then raise (Cycle (List.rev tmpl))
      else if S.mem n dones
      then (dones, sorted)
      else
        let tmps = S.add n tmps in
        let targets =
          match M.find_opt n g with
            | Some t -> S.elements t
            | None -> raise (Node_not_present n) in
        let dones, sorted =
          List.fold_left (traverse tmps tmpl) (dones, sorted) targets in
        (S.add n dones), n :: sorted in
    let _, sorted =
      M.fold (fun n _ (dones, sorted) ->
              traverse S.empty [] (dones, sorted) n
             ) g (S.empty, [])
    in sorted
end
