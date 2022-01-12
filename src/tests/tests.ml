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
                                        | {p.c := \"ngt 5\"})}", "C",
     "1234", V_record ["c", V_list [V_char 'g'; V_char 't'; V_char ' '; V_char '5']]);
  ]

let do_tests gen_ir exe_ir =
  let fails = ref 0 in
  let succs = ref 0 in
  let fail reason =
    incr fails;
    Printf.eprintf " failed, %s.\n%!" reason in
  let fail_ir ir reason =
    incr fails;
    Printf.eprintf " failed, %s.\n%!" reason;
    if   print_ir
    then Ir.Ir_printer.print_spec ir in
  let fail_match ir v v' =
    incr fails;
    Printf.eprintf " failed, incorrect result.\n%!";
    Printf.eprintf "  expected: %s\n%!" (Values.string_of_value v);
    Printf.eprintf "  got:      %s\n%!" (Values.string_of_value v');
    if   print_ir
    then Ir.Ir_printer.print_spec ir in
  let fail_except ir e =
    incr fails;
    Printf.eprintf " failed with exception: %s\n%!"
      (Runtime_exceptions.Internal_errors.error_msg e);
    if   print_ir
    then Ir.Ir_printer.print_spec ir in
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
                        | Some v' -> (match Builtins.eq lc "=" v v' with
                                        | Ok true  -> succ ()
                                        | Ok false -> fail_match ir v v'
                                        | Error e  -> fail_except ir e))

    ) tests;
  Printf.printf "Tests: %d failed out of %d.\n%!" !fails (!fails + !succs)
