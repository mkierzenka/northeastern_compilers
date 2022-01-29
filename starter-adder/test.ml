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
  t "add1" "(add1 4)" "5";
  t "sub1" "(sub1 4)" "3";
  t "sub_add" "(add1 (sub1 44))" "44";
  t "add_sub" "(sub1 (add1 40))" "40";
  t "add_add" "(add1 (add1 111))" "113";
  t "sub_sub" "(sub1 (sub1 1000))" "998";

  t "let" "(let ((x 10)) x)" "10";
  t "let_const" "(let ((a 7)) 71)" "71";

  te "let_empty" "(let (()) 2)" "expected list of bindings";
  te "let_no_binding_list" "(let (x 10) x)" "expected list of bindings";
  te "let_dup_binds" "(let ((x 1) (x 1)) 2)" "Duplicate symbol x";
  te "let_dup_binds2" "(let ((x 1) (x 3)) 2)" "Duplicate symbol x";

  te "unknown_keyword" "(word ((x 1)) x)" "paren must be followed by let, add, or sub";
  te "nested_unknown_keyword" "(let ((x 1)) (let ((y 1)) (add1 (blah y))))" "paren must be followed by let, add, or sub";
  te "nested_unknown_keyword2" "(let ((x 1)) (let ((y (bloh 2))) (add1 x)))" "paren must be followed by let, add, or sub";

  (* todo- use funs ti and tie to test the input files we have, andd add more such files *)
  ]
;;


let () =
  run_test_tt_main suite
;;
