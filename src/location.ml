open Lexing

type t = {
  loc_start: position;
  loc_end:   position;
  loc_ghost: bool;
}

let init lexbuf fname =
  lexbuf.lex_curr_p <- {
    pos_fname = fname;
    pos_lnum  = 1;
    pos_bol   = 0;
    pos_cnum  = 0;
  }

let curr lexbuf = {
  loc_start = lexbuf.lex_start_p;
  loc_end   = lexbuf.lex_curr_p;
  loc_ghost = false;
}

let _make_loc b e g = {
  loc_start = b;
  loc_end   = e;
  loc_ghost = g;
}

let make_loc b e = _make_loc b e false

let make_ghost_loc () = _make_loc Lexing.dummy_pos Lexing.dummy_pos true

let extent loc1 loc2 =
  make_loc loc1.loc_start loc2.loc_end

let get_pos_info pos =
  pos.pos_fname, pos.pos_lnum, pos.pos_cnum - pos.pos_bol

let print_curr_pos f lexbuf =
  let file, line, startchar = get_pos_info lexbuf.lex_curr_p in
  Printf.fprintf f "File \"%s\", line %d, character %d:"
                 file line startchar

let str_of_loc loc =
  let file, line, startchar = get_pos_info loc.loc_start in
  let endchar =
    loc.loc_end.pos_cnum - loc.loc_start.pos_cnum + startchar in
  Printf.sprintf "File \"%s\", line %d, characters %d-%d:"
                 file line startchar endchar

type 'a loc = {
  pelem: 'a;
  ploc:  t;
}

let mk_loc_val a l = {
  pelem = a;
  ploc  = l
}

let value l = l.pelem

let loc l = l.ploc
