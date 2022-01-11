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

let print_ir   = true

let tests = [
    ("trivial", "format { A := (# [\"A\"] #) }",  "A", "A",
     V_list [V_char 'A']);
    ("exact",   "format { A := (# [\"AB\"] #) }", "A", "ABC",
     V_list [V_char 'A'; V_char 'B']);
    ("astar",   "format { A := (# [\"A\"] #)* }", "A", "A",
     V_list [V_char 'A']);
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
    Printf.eprintf "  expected: %s\n%!" (Values.print v);
    Printf.eprintf "  got:      %s\n%!" (Values.print v');
    if   print_ir
    then Ir.Ir_printer.print_spec ir in
  let succ () =
    incr succs;
    Printf.eprintf " succeeded.\n%!" in
  List.iter (fun (test, spec, entry, data, v) ->
      Printf.eprintf "Running test '%s' ...%!" test;
      let ir = gen_ir test spec in
      match ir with
        | None    -> fail "no IR generated"
        | Some ir -> (match exe_ir test ir entry data with
                        | None    -> fail_ir ir "no value returned"
                        | Some v' -> if   v = v'
                                     then succ ()
                                     else fail_match ir v v')
    ) tests;
  Printf.printf "Tests: %d failed out of %d.\n%!" !fails (!fails + !succs)
