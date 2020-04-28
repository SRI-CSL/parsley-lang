module StringMap = Ast_utils.StringMap

(* generic variables are represented by an optional source variable
 * name and location (if derived from input source) and a ghost kind
 * (for type-safety).
 *)
module Tvar : sig

  type 'a t
  val mk_tvar: 'a -> string Location.loc -> 'a t
  val (=): 'a t -> 'a t -> bool
  val name: 'a t -> string Location.loc
  val to_string: 'a t -> string

end = struct

  type 'a t = {
    id:   int;
    name: string Location.loc;
  }

  let fresh = ref (StringMap.empty: int StringMap.t)

  let mk_tvar (kind: 'a) (name: string Location.loc) =
    let n = Location.value name in
    let id =
      match StringMap.find_opt n !fresh with
        | None -> 0
        | Some n -> n + 1 in
    fresh := StringMap.add n id !fresh;
    { id; name }

  let (=) a b =
    a.id == b.id && (Location.value a.name == Location.value b.name)

  let name v = v.name

  let to_string v =
    Printf.sprintf "%s@%d" (Location.value v.name) v.id
end
