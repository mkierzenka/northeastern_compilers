open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs

let t name program expected = name>::test_run program name expected;;

let ta name program_and_env expected = name>::test_run_anf program_and_env name expected;;

let te name program expected_err = name>::test_err program name expected_err;;

let tvg name program expected = name>::test_run_valgrind program name expected;;
  
let tanf name program expected = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

let tests = [
  te "unbound_id_l" "a" "The identifier a, used at";
  te "unbound_id_r" "a" ", is not in scope";
  te "unbound_fun_l" "f()" "The function name f, used at";
  te "unbound_fun_r" "f()" ", is not in scope";
  te "duplicate_id_l" "let x=1,x=2 in 3" "The identifier x, redefined at";
  te "duplicate_id_r" "let x=1,x=2 in 3" ", duplicates one at";
  te "duplicate_fun_l" "def f(): 2 def f(): 3 8" "The function name f, redefined at";
  te "duplicate_fun_r" "def f(): 2 def f(): 3 8" ", duplicates one at";
  te "arity_l" "def f(x): 2 f(4,5)" "The function called at";
  te "arity_r" "def f(x): 2 f(4,5)" "expected an arity of 1, but received 2 arguments";

  te "unbound_duplicate_id_unbl" "let x=1,x=2 in y" "The identifier y, used at";
  te "unbound_duplicate_id_unbr" "let x=1,x=2 in y" ", is not in scope";
  te "unbound_duplicate_id_dupl" "let x=1,x=2 in y" "The identifier x, redefined at";
  te "unbound_duplicate_id_dupr" "let x=1,x=2 in y" ", duplicates one at";
]

let suite =
"suite">:::tests
 



let () =
  run_test_tt_main ("all_tests">:::[suite; input_file_test_suite ()])
;;
