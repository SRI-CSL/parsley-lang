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

let _mk_loc b e g = {
  loc_start = b;
  loc_end   = e;
  loc_ghost = g;
}

let mk_loc b e = _mk_loc b e false

let ghost_loc = _mk_loc Lexing.dummy_pos Lexing.dummy_pos true

let extent loc1 loc2 =
  mk_loc
    (if loc1.loc_ghost then loc2.loc_start else loc1.loc_start)
    (if loc2.loc_ghost then loc1.loc_end else loc2.loc_end)

let loc_or_ghost = function
  | Some l -> l
  | None -> ghost_loc

let get_pos_info pos =
  pos.pos_fname, pos.pos_lnum, pos.pos_cnum - pos.pos_bol

let str_of_curr_pos lexbuf =
  let file, line, startchar = get_pos_info lexbuf.lex_curr_p in
  Printf.sprintf "File \"%s\", line %d, character %d"
                 file line startchar

let str_of_loc loc =
  let file, line, startchar = get_pos_info loc.loc_start in
  let endchar =
    loc.loc_end.pos_cnum - loc.loc_start.pos_cnum + startchar in
  Printf.sprintf "File \"%s\", line %d, characters %d-%d"
                 file line startchar endchar

let str_of_file_loc loc =
  let file, line, startchar = get_pos_info loc.loc_start in
  let endchar =
    loc.loc_end.pos_cnum - loc.loc_start.pos_cnum + startchar in
  Printf.sprintf "file \"%s\", line %d, characters %d-%d"
                 file line startchar endchar

type 'a loc = {
  pelem: 'a;
  ploc:  t;
}

let mk_loc_val a l = {
  pelem = a;
  ploc  = l
}

let mk_ghost a = {
  pelem = a;
  ploc = ghost_loc
}

let value l = l.pelem

let loc l = l.ploc
