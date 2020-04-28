(* basic graph module for dependency analysis *)

module type OrderedType = sig
    type t
    val compare: t -> t -> int
end

module type GraphType = sig
    (* The node is uniquely identified by its carrier 'a *)
    type node

    (* The graph type *)
    type t

    (* thrown by topo_sort *)
    exception Cycle of node list

    (* if node is *)
    exception Node_not_present of node

    val init: t

    (* the link is directional, from the first to the second node *)
    val add_link: t -> node -> node -> t

    (* the list of nodes linked to by a given node *)
    val targets: t -> node -> node list

    (* returns a topologically sorted node list if possible, raises
     * Cycle if not
     *)
    val topo_sort: t -> node list

  end

module Make (Ord : OrderedType) : GraphType
       with type node = Ord.t
