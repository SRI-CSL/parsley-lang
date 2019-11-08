(* utilities *)

module StringMap = Map.Make(struct type t = string
                                   let compare = compare
                            end)

let rec path_equals p1 p2 =
  match p1, p2 with
  | i1 :: r1, i2 :: r2 ->
        Location.value i1 = Location.value i2 && path_equals r1 r2
  | [], [] -> true
  | _, _   -> false

let path_loc p =
  let hd = List.hd p in
  let rec last = function
    | []    -> assert false
    | [e]   -> e
    | _::tl -> last tl
  in Location.extent (Location.loc hd) (Location.loc (last p))

let str_of_path p =
  String.concat "." (List.map (fun i -> Location.value i) p)
