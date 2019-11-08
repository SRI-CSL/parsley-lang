type t = {
  loc_start: Lexing.position;
  loc_end:   Lexing.position;
  loc_ghost: bool;
}

val init: Lexing.lexbuf -> string -> unit
val curr: Lexing.lexbuf -> t
val print_curr_pos: out_channel -> Lexing.lexbuf -> unit

val make_loc: Lexing.position -> Lexing.position -> t
val make_ghost_loc: Lexing.position -> Lexing.position -> t
val extent: t -> t -> t

type 'a loc = {
  pelem: 'a;
  ploc:  t;
}
val mk_loc_val:  'a -> t -> 'a loc
val value:       'a loc -> 'a
val loc:         'a loc -> t

val str_of_loc: t -> string
