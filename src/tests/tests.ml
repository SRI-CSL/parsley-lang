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

open Interpreter
open Values

let print_ir = true

let tests = [
    ("trivial", "format { A := (# [\"A\"] #) }",  "A",
     "A", V_list [V_char 'A']);
    ("exact",   "format { A := (# [\"AB\"] #) }", "A",
     "ABC", V_list [V_char 'A'; V_char 'B']);
    ("astar",   "format { A := (# [\"A\"] #)* }", "A",
     "A", V_list [V_char 'A']);
    ("istar",   "format { A := (# [\"0\" .. \"9\"] #)* }", "A",
     "0159A", V_list [V_char '0'; V_char '1'; V_char '5'; V_char '9']);
    ("ichoice", "format { A := (# [\"0\" | \"5\" | \"9\"] #)* }", "A",
     "0591A", V_list [V_char '0'; V_char '5'; V_char '9']);
    ("pure",  "format {Pure p {val: [byte]} := { p.val := \"A\" }}", "Pure",
     "", V_record ["val", V_list [V_char 'A']]);
    ("pure2", "format {Pure p {val: [byte] := []} := { p.val := \"A\" }}", "Pure",
     "", V_record ["val", V_list [V_char 'A']]);
    ("abc", "format {ABC p {a: [byte]} := !\"Helo\"! v=!\"ABC\"! {p.a := v}}", "ABC",
     "HeloABC", V_record ["a", V_list [V_char 'A'; V_char 'B'; V_char 'C']]);
    ("abc2", "format {ABC p {a: [byte]} := u=!\"Helo\"! v=!\"ABC\"! {p.a := List.concat(u,v)}}", "ABC",
     "HeloABC", V_record ["a", V_list [V_char 'H'; V_char 'e'; V_char 'l'; V_char 'o';
                                       V_char 'A'; V_char 'B'; V_char 'C']]);
    ("sum", "format {Add a {m: int} := x=Byte !\"+\"! y=Byte {a.m := Int.of_byte(x) + Int.of_byte(y)}}",
     "Add", "5+6", V_record ["m",V_int (Int64.of_int (Char.code '5' + Char.code '6'))]);
    ("struct", "format {Struct s {x: int, y: [byte]} := x=Byte y=!\"Helo\"! {s.x := Int.of_byte(x); s.y := y}}",
     "Struct", "ZHelo", V_record ["x", V_int (Int64.of_int (Char.code 'Z'));
                                  "y", V_list [V_char 'H'; V_char 'e'; V_char 'l'; V_char 'o']]);
    ("depvec", "format {DepVec d {v: [byte]} := c=Byte v=(Byte ^ Int.of_byte(c)) {d.v := v}}",
     "DepVec", "\003abcd", V_record ["v", V_list [V_char 'a'; V_char 'b'; V_char 'c']]);
    ("constr", "fun more_than_five(b : [byte]) -> bool = {
                  (case Int.of_bytes(b) of
                   | option::Some(i) -> i > 5
                   | option::None()  -> bool::False())
                }
                format {C p {c:[byte]} := i=(# [\"0\" .. \"9\" ]* #)
                                          (([more_than_five(i)] {p.c := \"gt 5\"})
                                        | {p.c := \"ngt 5\"})}",
     "C", "1234", V_record ["c", V_list [V_char 'g'; V_char 't'; V_char ' '; V_char '5']]);
    ("recdnt", "type recd = {t: byte}
                format {NonTerm nt {recd} := c=Byte {nt.t := c}}",
     "NonTerm", "B", V_record ["t", V_char 'B']);
    ("depntvec", "type recd = {t: byte}
                  fun byte_of_recd(r: recd) -> byte = {r.t}
                  format {NonTerm n {recd} := c=Byte {n.t := c};;
                          DepNTVec d {v: [byte]} :=
                            c=Byte v=(NonTerm ^ Int.of_byte(c))
                            {d.v := List.map(byte_of_recd, v)}}",
     "DepNTVec", "\002AB", V_record ["v", V_list [V_char 'A'; V_char 'B']]);
    ("ntdepntvec", "type recd = {t: byte}
                    fun byte_of_recd(r: recd) -> byte = {r.t}
                    format {NonTerm n {recd} := c=Byte {n.t := c};;
                            NTDepNTVec d {v: [byte]} :=
                              c=NonTerm v=(NonTerm ^ Int.of_byte(c.t))
                              {d.v := List.map(byte_of_recd, v)}}",
     "NTDepNTVec","\002AB", V_record ["v", V_list [V_char 'A'; V_char 'B']]);
    ("bitvector", "bitfield bf = {top: 8:7, bot: 6:0}
                   format {N n {v: bitvector<7>, f: bf, t: bitvector<2>, b: bitvector<7>} :=
                             BitVector<1> $align<8> v=BitVector<7> f=$bitfield(bf)
                             {n.v := v; n.f := f; n.t := f.top; n.b := f.bot}}",
     "N", "\x00\x43\x03", let bf = Typing.TypingEnvironment.(
                              {bf_name   = "bf";
                               bf_fields = [("top", (8,7)); ("bot", (6,0))];
                               bf_length = 9}) in
                          V_record ["v", V_bitvector [false;true;false;false;false;false;true];
                                    "f", V_bitfield (bf, [true;false;false;false;false;false;false;true;true]);
                                    "t", V_bitvector [true;false];
                                    "b", V_bitvector [false;false;false;false;false;true;true]]);
    ("choice1", "type choice = | Good of [byte] | Bad of [byte]
                 format {Chk r {v: [byte]} :=
                        (|res : choice := choice::Good(\"\")|)
                        ((!\"G\"! {res := choice::Good(\"G\")})
                        |(!\"B\"! {res := choice::Bad(\"B\")})
                        )
                        (([res ~~ choice::Good] {r.v := \"Succ\"})
                        |([res ~~ choice::Bad]  {r.v := \"Fail\"})
                        )}",
     "Chk", "G", V_record ["v", V_list[V_char 'S'; V_char 'u'; V_char 'c'; V_char 'c']]);
    ("choice2", "type choice = | Good of [byte] | Bad of [byte]
                 format {Chk r {v: [byte]} :=
                        (|res : choice := choice::Good(\"\")|)
                        ((!\"G\"! {res := choice::Good(\"G\")})
                        |(!\"B\"! {res := choice::Bad(\"B\")})
                        )
                        (([res ~~ choice::Good] {r.v := \"Succ\"})
                        |([res ~~ choice::Bad]  {r.v := \"Fail\"})
                        )}",
     "Chk", "B", V_record ["v", V_list[V_char 'F'; V_char 'a'; V_char 'i'; V_char 'l']]);
    ("views1", "format {P1 := (# [\"0\" .. \"5\"]* #);;
                        P2 := (# [\"0\" .. \"9\"]* #);;
                        Twice pt {p1: [byte], p2: [byte]} :=
                          w={;; View.get_current()}
                          v={;; View.clone(w)}
                          p1=@[w, P1]
                          p2=@[v, P2]
                          {pt.p1 := p1; pt.p2 := p2}}",
     "Twice", "5091a", V_record ["p1", V_list[V_char '5'; V_char '0'];
                                 "p2", V_list[V_char '5'; V_char '0'; V_char '9'; V_char '1']]);
    ("views2a", "format {LetterFill lf {s: [byte], t: [byte]} :=
                             v = {;; View.get_current() }
                             w = {;; View.restrict(v, 0, 3)}
                          next = {;; View.restrict_from(v, 3)}
                          s=@[w,    (# [\"0\" .. \"5\"]* [\" \"]* #)]
                          {lf.s := s}
                          t=@[next, (# [\"5\" .. \"9\"]* [\" \"]* #)]
                          {lf.t := t}}",
     "LetterFill", "01a59b", V_record ["s", V_list[V_char '0'; V_char '1'];
                                       "t", V_list[V_char '5'; V_char '9']]);
    ("views2b", "format {LetterFill lf {s: [byte], t: [byte]} :=
                             v = {;; View.get_current() }
                             w = {;; View.restrict(v, 0, 3)}
                          next = {;; View.restrict_from(v, 3)}
                          s=@[w,    (# [\"0\" .. \"5\"]* [\" \"]* #)]
                          {lf.s := s}
                          @^[next]
                          t=(# [\"5\" .. \"9\"]* [\" \"]* #)
                          {lf.t := t}}",
     "LetterFill", "01a59b", V_record ["s", V_list[V_char '0'; V_char '1'];
                                       "t", V_list[V_char '5'; V_char '9']]);
    ("views3", "format {LetterFill lf (o: int, n : int) {s: [byte], t: [byte]} :=
                               v = {;; View.get_current()}
                               w = {;; View.restrict(v, o, n)}
                               next = {;; View.restrict_from(v, n)}
                               s=@[w, (# [\"0\" .. \"9\"]* [\" \"]* #)]
                               {lf.s := s}
                               @^[next]
                               t=(# [\"0\" .. \"9\"]* [\" \"]* #)
                               {lf.t := t};;
                        Letters ls {ls: [byte], lt: [byte]} :=
                             l=LetterFill<n=3,o=0>
                             {ls.ls := l.s; ls.lt := l.t}}",
     "Letters", "01a59b",  V_record ["ls", V_list[V_char '0'; V_char '1'];
                                     "lt", V_list[V_char '5'; V_char '9']]);
     ("offs", "format {OffsetTest ot {a: int, b:int} :=
                         a={;; View.get_current_cursor()}
                         !\"AA\"!
                         b={;; View.get_current_cursor()}
                         {ot.a := a; ot.b := b}}",
     "OffsetTest", "AA", V_record ["a", V_int 0L;
                                   "b", V_int 2L]);
    ("int", "format {I16LE := Int16<endian=endian::Little()>;;
                     I16BE := Int16<endian=endian::Big()>;;
                     U16LE := UInt16<endian=endian::Little()>;;
                     U16BE := UInt16<endian=endian::Big()>;;
                     TInt t {i:int, j:int, k:int, l:int, m:int, n:int} :=
                        i=Int8 j=UInt8 k=I16LE l=I16BE m=U16LE n=U16BE
                        {t.i := i; t.j := j; t.k := k; t.l := l; t.m := m; t.n := n}}",
     "TInt", "\x80\x80\x01\x80\x01\x80\x01\x80\x01\x80",
     V_record ["i", V_int 0xffffffffffffff80L; "j", V_int 0x80L; "k", V_int 0xffffffffffff8001L;
               "l", V_int 0x0180L; "m", V_int 0x8001L; "n", V_int 0x0180L]);
    ("uint1", "format {U32LE := UInt32<endian=endian::Little()>;;
                       U32BE := UInt32<endian=endian::Big()>;;
                       TInt t {i: int, j:int} :=
                          i=U32LE j=U32BE {t.i := i; t.j := j}}",
     "TInt", "\x00\x01\x02\x80\x00\x01\x02\x80", V_record ["i", V_int 0x80020100L;
                                                           "j", V_int 0x00010280L]);
    ("int1", "format {I32LE := Int32<endian=endian::Little()>;;
                      I32BE := Int32<endian=endian::Big()>;;
                      TInt t {i: int, j:int} :=
                         i=I32LE j=I32BE {t.i := i; t.j := j}}",
     "TInt", "\x00\x01\x02\x80\x00\x01\x02\x80", V_record ["i", V_int 0xffffffff80020100L;
                                                           "j", V_int 0x00010280L]);
    ("uint2", "format {U64LE := UInt64<endian=endian::Little()>;;
                       U64BE := UInt64<endian=endian::Big()>;;
                       TInt t {i: int, j:int} :=
                          i=U64LE j=U64BE {t.i := i; t.j := j}}",
     "TInt", "\x00\x01\x02\x80\x00\x01\x02\x40\x00\x01\x02\x80\x00\x01\x02\x80",
     V_record ["i", V_int 0x4002010080020100L;
               "j", V_int 0x0001028000010280L]);
    ("int2", "format {I64LE := Int64<endian=endian::Little()>;;
                      I64BE := Int64<endian=endian::Big()>;;
                      TInt t {i: int, j:int} :=
                         i=I64LE j=I64BE {t.i := i; t.j := j}}",
     "TInt", "\x00\x01\x02\x80\x00\x01\x02\x40\x00\x01\x02\x80\x00\x01\x02\x80",
     V_record ["i", V_int 0x4002010080020100L;
               "j", V_int 0x0001028000010280L]);
    ("views1", "format {U32LE := UInt32<endian=endian::Little()>;;
                        TInt t {i: int} :=
                           i=@(1, U32LE)
                           {t.i := i}}",
     "TInt", "\000\001\002\003\004\005", V_record ["i", V_int 0x04030201L]);
    ("views2", "format {U32LE := UInt32<endian=endian::Little()>;;
                        TInt t {i: int} :=
                           Byte // affects view
                           v={;; let v = View.get_current() in
                                 View.restrict(v, 0, 4)}
                           Byte // does not affect view
                           i=@[v, U32LE]
                           {t.i := i}}",
     "TInt", "\000\001\002\003\004\005", V_record ["i", V_int 0x04030201L]);
    ("views3", "fun mk_views() -> [view] = {
                   let v  = View.get_current() in
                   let v0 = View.restrict(v, 0, 4) in
                   let v1 = View.restrict(v, 4, 4) in
                   let v2 = View.restrict(v, 8, 4) in
                   let v3 = View.restrict(v, 12, 4) in
                   [v2; v3; v0; v1]
                }
                format {U32BE := UInt32<endian=endian::Big()>;;
                        TInt t {is: [int]} :=
                           vs={;; mk_views()}
                           is=@#[vs, U32BE]
                           {t.is := is}}",
     "TInt", "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f",
     V_record ["is", V_list [V_int 0x08090a0bL; V_int 0x0c0d0e0fL;
                             V_int 0x00010203L; V_int 0x04050607L]]);
    ("views4", "fun mk_views() -> [view] = {
                   let v  = View.get_current() in
                   let v0 = View.restrict(v, 0, 4) in
                   let v1 = View.restrict(v, 4, 4) in
                   let v2 = View.restrict(v, 8, 4) in
                   let v3 = View.restrict(v, 12, 4) in
                   [v2; v3; v0; v1]
                }
                fun mk_args() -> [int] = { [1;2;3;4] }
                type recd = {v: int, a: int}
                format { U32BE := UInt32<endian=endian::Big()>;;
                         TInt  t (a: int) {recd} := v=U32BE {t.v := v; t.a := a};;
                         TInts t {rs: [recd]} :=
                            vs={;; mk_views ()}
                            rs=@#[vs, TInt<a <- (mk_args ())>]
                            {t.rs := rs}}",
     "TInts", "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f",
     V_record ["rs", V_list [V_record ["a", V_int 0x1L;
                                       "v", V_int 0x08090a0bL];
                             V_record ["a", V_int 0x2L;
                                       "v", V_int 0x0c0d0e0fL];
                             V_record ["a", V_int 0x3L;
                                       "v", V_int 0x00010203L];
                             V_record ["a", V_int 0x4L;
                                       "v", V_int 0x04050607L]]]);
    ("rules1", "format {N n {s: [byte]} :=
                        Byte !\"AB\"! {n.s := \"ab\"}
                      ; Byte !\"CD\"! {n.s := \"cd\"}
                      ; Byte !\"EF\"! {n.s := \"ef\"}
                      ;               {n.s := \"de\"}}",
     "N", "_CD", V_record ["s", V_list [V_char 'c'; V_char 'd']]);
    ("rules2", "format {N n {s: [byte]} :=
                        Byte !\"AB\"! {n.s := \"ab\"}
                      ; Byte !\"CD\"! {n.s := \"cd\"}
                      ; Byte !\"EF\"! {n.s := \"ef\"}
                      ;               {n.s := \"de\"}}",
     "N", "_EF", V_record ["s", V_list [V_char 'e'; V_char 'f']]);
    ("rules3", "format {N n {s: [byte]} :=
                        Byte !\"AB\"! {n.s := \"ab\"}
                      ; Byte !\"CD\"! {n.s := \"cd\"}
                      ; Byte !\"EF\"! {n.s := \"ef\"}
                      ;               {n.s := \"de\"}}",
     "N", "FE", V_record ["s", V_list [V_char 'd'; V_char 'e']]);
    ("recfun", "type t = | A | B
                recfun do_A(t: t) -> int = {
                  (case t of
                  | t::A() -> 1
                  | t::B() -> do_B(t)
                  )
                }
                and do_B(t: t) -> int = {
                  (case t of
                  | t::A() -> do_A(t)
                  | t::B() -> 2
                  )
                }
                type r = {i: int}
                format {A a {r} :=
                            !\"AA\"! {a.i := do_A(t::A())}
                          ; !\"AB\"! {a.i := do_A(t::B())}
                          ; !\"BA\"! {a.i := do_B(t::A())}
                          ; !\"BB\"! {a.i := do_B(t::B())}
                          ;;
                        R r {r: [r]} :=
                            r1=A r2=A r3=A r4=A
                            {r.r := [r1; r2; r3; r4]}}",
     "R", "BBBAABAA", V_record ["r", V_list [V_record ["i", V_int 2L];
                                             V_record ["i", V_int 1L];
                                             V_record ["i", V_int 2L];
                                             V_record ["i", V_int 1L]]]);
    ("map2", "type t = | A | B
              fun couple (l: t, r: t) -> int = {
                 (case (l, r) of
                 | (t::A(), t::A()) -> 0
                 | (t::A(), t::B()) -> 1
                 | (t::B(), t::A()) -> 2
                 | (t::B(), t::B()) -> 3
                 )
              }
              format {A a {i: [int]} := {
                         let l = [t::A(); t::B(); t::A(); t::B()] in
                         let r = [t::A(); t::A(); t::B(); t::B()] in
                         a.i := List.map2(couple, l, r) }}",
     "A", "", V_record ["i", V_list [V_int 0L; V_int 2L; V_int 1L; V_int 3L]]);
    ("ws_empty", "format {WS w (allow_empty: bool) {ws: [byte]}:=
                            [allow_empty]
                            ws=(# [\" \" | \"\t\" | \"\r\" | \"\n\"]* #)
                            {w.ws := ws}
                          ; [!allow_empty]
                            ws=(# [\" \" | \"\t\" | \"\r\" | \"\n\"]+ #)
                            {w.ws := ws}
                          ;;
                          A := !\"[\"!;; B := !\"]\"!;; C := !\"+\"!;; D := !\"-\"!;;
                          #[whitespace(WS:allow_empty=true)]
                          NT n {a: int} :=  A B              {n.a := 1}
                                        ;  ((A C) | (B D))*  {n.a := 2}}",
     "NT", "[]", V_record ["a", V_int 1L]);
    ("ws_empty", "format {WS w (allow_empty: bool) {ws: [byte]}:=
                            [allow_empty]
                            ws=(# [\" \" | \"\t\" | \"\r\" | \"\n\"]* #)
                            {w.ws := ws}
                          ; [!allow_empty]
                            ws=(# [\" \" | \"\t\" | \"\r\" | \"\n\"]+ #)
                            {w.ws := ws}
                          ;;
                          A := !\"[\"!;; B := !\"]\"!;; C := !\"+\"!;; D := !\"-\"!;;
                          #[whitespace(WS:allow_empty=true)]
                          NT n {a: int} :=  A B              {n.a := 1}
                                        ;  ((A C) | (B D))*  {n.a := 2}}",
     "NT", "[ ]", V_record ["a", V_int 1L]);
    ("ws_noempty", "format {WS w (allow_empty: bool) {ws: [byte]}:=
                            [allow_empty]
                            ws=(# [\" \" | \"\t\" | \"\r\" | \"\n\"]* #)
                            {w.ws := ws}
                          ; [!allow_empty]
                            ws=(# [\" \" | \"\t\" | \"\r\" | \"\n\"]+ #)
                            {w.ws := ws}
                          ;;
                          A := !\"[\"!;; B := !\"]\"!;; C := !\"+\"!;; D := !\"-\"!;;
                          #[whitespace(WS:allow_empty=false)]
                          NT n {a: int} :=  A B              {n.a := 1}}",
     "NT", " [ ] ", V_record ["a", V_int 1L]);
  ]

let do_tests gen_ir exe_ir =
  let fails = ref 0 in
  let succs = ref 0 in
  let print_ir ir =
    if   print_ir
    then Ir.Ir_printer.print_spec ir in
  let fail reason =
    incr fails;
    Printf.eprintf " failed, %s.\n%!" reason in
  let fail_ir ir reason =
    incr fails;
    Printf.eprintf " failed, %s.\n%!" reason;
    print_ir ir in
  let fail_match ir v v' =
    incr fails;
    Printf.eprintf " failed, incorrect result.\n%!";
    Printf.eprintf "expected:\n   %s\n%!" (Values.string_of_value v);
    Printf.eprintf "got:     \n   %s\n%!" (Values.string_of_value v');
    print_ir ir in
  let fail_except ir e =
    incr fails;
    Printf.eprintf " failed with exception: %s\n%!"
      (Runtime_exceptions.Internal_errors.error_msg e);
    print_ir ir in
  let succ () =
    incr succs;
    Printf.eprintf " passed.\n%!" in
  List.iter (fun (test, spec, entry, data, v) ->
      Printf.eprintf "Running test '%s' ...%!" test;
      let ir = gen_ir test spec in
      match ir with
        | None    -> fail "no IR generated"
        | Some ir -> (let lc = Parsing.Location.ghost_loc in
                      match exe_ir test ir entry data with
                        | None    -> fail_ir ir "no value returned"
                        | Some v' -> match Builtins.eq lc "=" v v' with
                                       | Ok true  -> succ ()
                                       | Ok false -> fail_match ir v v'
                                       | Error e  -> fail_except ir e)

    ) tests;
  Printf.printf "Tests: %d failed out of %d.\n%!" !fails (!fails + !succs)
