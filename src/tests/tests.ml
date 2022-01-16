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

open Typing.TypingEnvironment
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
     "N", "\x00\x43\x03", let bf = {bf_name   = "bf";
                                    bf_fields = [("top", (8,7)); ("bot", (6,0))];
                                    bf_length = 9} in
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
