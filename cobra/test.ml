open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs


(* Runs a program, given as a source string, and compares its output to expected *)
let t (name : string) (program : string) (expected : string) = name>::test_run program name expected;;

(* Runs a program, given as an ANFed expr, and compares its output to expected *)
let ta (name : string) (program : tag expr) (expected : string) = name>::test_run_anf program name expected;;

(* Runs a program, given as a source string, and compares its error to expected *)
let te (name : string) (program : string) (expected_err : string) = name>::test_err program name expected_err;;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf (name : string) (program : 'a expr) (expected : unit expr) = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_expr;;

(* Checks if two strings are equal *)
let teq (name : string) (actual : string) (expected : string) = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to expected *)
let tprog (filename : string) (expected : string) = filename>::test_run_input filename expected;;

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to expected *)
let teprog (filename : string) (expected : string) = filename>::test_err_input filename expected;;

let max_snake_num = (Int64.div Int64.max_int 2L)
let max_snake_num_plus_one = Int64.add max_snake_num 1L
let min_snake_num = (Int64.div Int64.min_int 2L)
let min_snake_num_minus_one = Int64.sub min_snake_num 1L

let str_max_snake_num = (Int64.to_string max_snake_num)
let str_max_snake_num_plus_one = (Int64.to_string max_snake_num_plus_one)
let str_min_snake_num = (Int64.to_string min_snake_num)
let str_min_snake_num_minus_one = (Int64.to_string min_snake_num_minus_one)

let forty = "let x = 40 in x"
let neg_forty = "let x = -40 in x"
let fals = "let x = false in x"
let tru = "let x = true in x"

let suite =
"unit_tests">:::
 [
  (* basic value reporting *)
  t "forty" forty "40";
  t "neg_fory" neg_forty "-40";
  t "fals" fals "false";
  t "tru" tru "true";
  t "max_snake_int" str_max_snake_num str_max_snake_num;
  t "min_snake_int" str_min_snake_num str_min_snake_num;

  (* edge case tests for compile time integer overflow *)
  t "max_snake_num" str_max_snake_num str_max_snake_num;
  te "overflow_max_snake_num_plus_one"
    str_max_snake_num_plus_one
    str_max_snake_num_plus_one;
  t "min_snake_num" str_min_snake_num str_min_snake_num;
  te "underflow_min_snake_num_minus_one"
    str_min_snake_num_minus_one
    str_min_snake_num_minus_one;

  (* edge case tests for runtime integer overflow *)
  te "add1_overflow" (sprintf "add1(%s)" str_max_snake_num) "overflow";
  te "sub1_overflow" (sprintf "sub1(%s)" str_min_snake_num) "overflow";
  te "sub_add_overflow"
    (sprintf "let x=sub1(%s) in add1(add1(x))" str_max_snake_num)
    "overflow";
  te "overflow_in_value"
    (sprintf "let x=add1(%s) in 8" str_max_snake_num)
    "overflow";
  te "overflow_in_plus"
    (sprintf "%s + 1" str_max_snake_num)
    "overflow";
  te "overflow_in_plus_flipped"
    (sprintf "1 + %s" str_max_snake_num)
    "overflow";
  te "overflow_in_plus2"
    (sprintf "let x= 1 + %s in 98" str_max_snake_num)
    "overflow";
  te "overflow_in_minus"
    (sprintf "print(0 - %s)" str_min_snake_num)
    "overflow";
  te "overflow_in_times"
    (sprintf "2 * %s" str_max_snake_num)
    "overflow";
  te "underflow_in_plus"
    (sprintf "let x= -1 + %s in 98" str_min_snake_num)
    "overflow";
  te "underflow_in_minus"
    (sprintf "%s - 1" str_min_snake_num)
    "overflow";
  te "underflow_in_times"
    (sprintf "2 * %s" str_min_snake_num)
    "overflow";

  (* print tests *)
  t "print_5" "print(5)" "5\n5";
  t "print_-5" "print(-5)" "-5\n-5";
  t "print_true" "print(true)" "true\ntrue";
  t "print_false" "print(false)" "false\nfalse";
  t "print_let_val" "let x=(print(6)) in 9" "6\n9";
  t "nested_print_let_val"
      "let x = 1 in (let y = print(x + 1) in print(y + 2))"
      "2\n4\n4";
  t "print_mul" "print(7 * 9)" "63\n63";

  (* arithmetric tests *)
  t "plus" "4 + 9" "13";
  t "minus" "4 - 9" "-5";
  t "times" "4 * 9" "36";
  t "add1" "add1(8)" "9";
  t "sub1" "sub1(8)" "7";
  t "add_sub_edge" (sprintf "add1(sub1(%s)) + 0" str_max_snake_num) str_max_snake_num;
  te "plus_err" "4 + false" "arithmetic expected a number";
  te "minus_err" "(true && false) - 9" "arithmetic expected a number";
  te "times_err" "4 * true" "arithmetic expected a number";
  te "add1_err" "add1(false || false)" "arithmetic expected a number";
  te "sub1_err" "sub1(false)" "arithmetic expected a number";

  (* and tests *)
  t "and_ff" "false && false" "false";
  t "and_ft" "false && true" "false";
  t "and_tf" "true && false" "false";
  t "and_tt" "true && true" "true";
  t "and_side_effect" "true && print(true)" "true\ntrue";
  te "and_num" "true && 2" "logic expected a boolean";
  te "and_num2" "(true && true) && 3" "logic expected a boolean";
  te "and_num_flipped" "2 && true" "logic expected a boolean";
  t "and_short_circuit" "false && print(2)" "false";
  t "and_short_circuit1" "false && 8" "false";

  (* or tests *)
  t "or_ff" "false || false" "false";
  t "or_ft" "false || true" "true";
  t "or_tf" "true || false" "true";
  t "or_tt" "true || true" "true";
  t "or_side_effects" "print(false) || print(true) && print(false)" "false\ntrue\nfalse\nfalse";
  te "or_num" "false || 8" "logic expected a boolean";
  te "or_num_flipped" "8 || false" "logic expected a boolean";
  t "or_short_circuit_1" "true || 8" "true";
  t "or_short_circuit_2" "true || print(2)" "true";

  (* eq tests *)
  t "eq_1" "2 == 2" "true";
  t "eq_2" "2 == 3" "false";
  t "eq_3" "3 == 2" "false";
  t "eq_4" "33 == 32" "false";
  t "eq_5" "88 == 88" "true";
  t "eq_6" "0 == false" "false";
  t "eq_7" "true == 1" "false";
  t "eq_8" "true == true" "true";
  t "eq_9" "false == false" "true";
  t "eq_10" "false == true" "false";
  t "eq_11" "(-5 == -4) == !(3 == 3)" "true";
  t "eq_12" "(-5 == -4) == (3 == 3)" "false";

  (* greater tests *)
  t "greater_1" "2 > 2" "false";
  t "greater_2" "2 > 3" "false";
  t "greater_3" "3 > 2" "true";
  t "greater_4" "33 > 32" "true";
  t "greater_5" "88 > 88" "false";
  te "greater_er_1" "88 > true" "arithmetic expected a number";
  te "greater_er_2" "(1 == 1) > 2" "arithmetic expected a number";

  (* greater eq tests *)
  t "greater_eq_1" "2 >= 2" "true";
  t "greater_eq_2" "2 >= 3" "false";
  t "greater_eq_3" "3 >= 2" "true";
  t "greater_eq_4" "33 >= 32" "true";
  t "greater_eq_5" "88 >= 88" "true";
  te "greater_eq_er_1" "88 > (9 == 8)" "arithmetic expected a number";
  te "greater_eq_er_2" "true > 2" "arithmetic expected a number";

  (* less tests *)
  t "less_1" "2 < 2" "false";
  t "less_2" "2 < 3" "true";
  t "less_3" "3 < 2" "false";
  t "less_4" "33 < 32" "false";
  t "less_5" "88 < 88" "false";
  te "less_er_1" "88 < (1 == 1)" "arithmetic expected a number";
  te "less_er_2" "(1 == -1) < 2" "arithmetic expected a number";

  (* less eq tests *)
  t "less_eq_1" "2 <= 2" "true";
  t "less_eq_2" "2 <= 3" "true";
  t "less_eq_3" "3 <= 2" "false";
  t "less_eq_4" "33 <= 32" "false";
  t "less_eq_5" "88 <= 88" "true";
  te "less_eq_er_1" "88 <= (1 == 1)" "arithmetic expected a number";
  te "less_eq_er_2" "(1 == -1) <= 2" "arithmetic expected a number";

  (* not tests *)
  t "not_t" "!(true)" "false";
  t "not_f" "!(false)" "true";
  t "not1" "!(2 == 3)" "true";
  t "not2" "!(3 == 3)" "false";
  te "not_err1" "!(1 + 2)" "logic expected a boolean";

  (* if tests *)
  t "if_consts1" "if true: 5 else: 7" "5";
  t "if_consts2" "if false: 5 else: 7" "7";
  t "if_consts3" "if true: false else: true" "false";
  t "if_consts4" "if false: false else: true" "true";
  t "if_consts5" "if 2 < 3: add1(6 + 7) else: sub1(7 * 8)" "14";
  te "if_num_err" "if 1: true else: false" "if expected a boolean";

  (* if not-eager eval tests *)
  t "if_eager_consts1" "if true: 5 else: print(7)" "5";
  t "if_eager_consts2" "if false: print(5) else: 7" "7";
  t "if_eager_consts3" "if 2 < 3: add1(6 + 7) else: sub1(print(7) * 8)" "14";
  t "if_eager_consts4" "if 2 < 3: add1(6 + 7) else: sub1(7 * print(8))" "14";
  t "if_eager_consts5" "if 2 < 3: add1(6 + 7) else: print(sub1(7 * 8))" "14";

  (* compound tests *)
  t "compound_1" "true || false == true" "true";
  t "compound_2" "(true || false) == true" "true";
  t "compound_3" "(true || false) == 88" "false";

  t "order_ops_1" "let z=true in false || z" "true";
  te "order_ops_2" "(let z=true in false) || z" "is not in scope";
 ]
;;


(* input_file_test_suite () will run all the tests in the subdirectories of input/ *)
let () =
  run_test_tt_main ("all_tests">:::[suite; input_file_test_suite ()])
;;
