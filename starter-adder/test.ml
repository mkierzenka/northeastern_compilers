open Compile
open Runner
open Printf
open OUnit2

(* Runs a program, given as a source string, and compares its output to expected *)
let t (name : string) (program : string) (expected : string) : OUnit2.test =
  name>::test_run program name expected;;
(* Runs a program, given as a source string, and compares its error to expected *)
let te (name : string) (program : string) (expected_err : string) : OUnit2.test =
  name>::test_err program name expected_err;;

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to expected *)
let ti (filename : string) (expected : string) = filename>::test_run_input filename expected;;
(* Runs a program, given as the name of a file in the input/ directory, and compares its error to expected *)
let tie (filename : string) (expected_err : string) = filename>::test_err_input filename expected_err;;


let suite : OUnit2.test =
"suite">:::
 [t "forty_one" "41" "41";
  t "let_const" "(let ((a 7)) 71)" "71";
  t "add1" "(add1 4)" "5";
  t "sub1" "(sub1 4)" "3";
  t "sub_add" "(add1 (sub1 44))" "44";
  t "add_sub" "(sub1 (add1 40))" "40";
  t "add_add" "(add1 (add1 111))" "113";
  t "sub_sub" "(sub1 (sub1 1000))" "998";

  t "nyi" "(let ((x 10)) x)" "10";

  te "let_empty" "(let (()) 2)" "Syntax error on bindings";
  ]
;;


let () =
  run_test_tt_main suite
;;
