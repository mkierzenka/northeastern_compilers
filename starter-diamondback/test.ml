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

  (* basic value reporting *)
  t "forty" forty "40";
  t "neg_fory" neg_forty "-40";
  t "fals" fals "false";
  t "tru" tru "true";
  t "max_snake_int" str_max_snake_num str_max_snake_num;
  t "min_snake_int" str_min_snake_num str_min_snake_num;
  te "unbound_id" "v" "is not in scope";

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

  (* isnum/isbool *)
  t "isnum1" "isnum(0)" "true";
  t "isnum2" "isnum(-2)" "true";
  t "isnum3" "isnum(9 + add1(2))" "true";
  t "isnum4" "isnum(true && false)" "false";
  t "isnum5" "isnum(true && true)" "false";
  t "isnum6" (sprintf "isnum(%s)" str_max_snake_num) "true";
  t "isnum7" (sprintf "isnum(%s)" str_min_snake_num) "true";
  t "isbool1" "isbool(true)" "true";
  t "isbool2" "isbool(false)" "true";
  t "isbool3" "isbool(false || (add1(1) == 3))" "true";
  t "isbool4" "isbool(isnum(7))" "true";
  t "isbool5" "isbool(7)" "false";
  t "isbool6" "isbool(0)" "false";
  t "isbool7" "isbool(2 + 3)" "false";
  t "isbool8" (sprintf "isbool(%s)" str_max_snake_num) "false";
  t "isbool9" (sprintf "isbool(%s)" str_min_snake_num) "false";
]

let suite =
"suite">:::tests
 



let () =
  run_test_tt_main ("all_tests">:::[suite; input_file_test_suite ()])
;;
