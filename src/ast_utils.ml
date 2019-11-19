(* utilities *)

module StringMap = Map.Make(struct type t = string
                                   let compare = compare
                            end)

let rec path_compare p1 p2 =
  match p1, p2 with
    | [], _::_ -> -1
    | _::_, [] -> 1
    | [], []   -> 0
    | i1 :: r1, i2 :: r2 ->
          (let c = compare (Location.value i1) (Location.value i2) in
           if c <> 0
           then c
           else path_compare r1 r2)

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

let param_lookup id param_decls =
  let rec scan decls =
    match decls with
      | [] ->
            None
      | decl :: rest ->
            let param, te = Location.value decl in
            if Location.value id = Location.value param
            then Some te
            else scan rest
  in scan param_decls

(* Decompose a path into a non-terminal ident and its attribute, if
 * possible.  We rely on non-terminals being uppercase, and paths and
 * idents being non-empty.
 *)
let path_into_nterm_attr p =
  match List.rev p with
    | [] ->
          assert false
    | [nt] ->
          let id = Location.value nt in
          assert (Char.uppercase_ascii id.[0] = id.[0]);
          p, None
    | a::nt::tl ->
          let id = Location.value a in
          if Char.uppercase_ascii id.[0] = id.[0]
          then p, None
          else List.rev (nt :: tl), Some a
