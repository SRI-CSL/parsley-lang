type t

val init: Lexing.lexbuf -> string -> unit
val curr: Lexing.lexbuf -> t
val str_of_curr_pos: Lexing.lexbuf -> string

val make_loc: Lexing.position -> Lexing.position -> t
val make_ghost_loc: unit -> t
val extent: t -> t -> t

type 'a loc

val mk_loc_val:  'a -> t -> 'a loc
val value:       'a loc -> 'a
val loc:         'a loc -> t

val str_of_loc:      t -> string (* full location, including file name *)
val str_of_file_loc: t -> string (* location without file name *)
