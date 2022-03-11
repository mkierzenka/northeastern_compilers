open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors

let t name program input expected = name>::test_run ~args:[] ~std_input:input program name expected;;
let ta name program input expected = name>::test_run_anf ~args:[] ~std_input:input program name expected;;
let tgc name heap_size program input expected = name>::test_run ~args:[string_of_int heap_size] ~std_input:input program name expected;;
let tvg name program input expected = name>::test_run_valgrind ~args:[] ~std_input:input program name expected;;
let tvgc name heap_size program input expected = name>::test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input program name expected;;
let terr name program input expected = name>::test_err ~args:[] ~std_input:input program name expected;;
let tgcerr name heap_size program input expected = name>::test_err ~args:[string_of_int heap_size] ~std_input:input program name expected;;
let tanf name program input expected = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

let pair_tests = [
  t "tup1" "let t = (4, (5, 6)) in
            begin
              t[0] := 7;
              t
            end" "" "(7, (5, 6))";
  t "tup2" "let t = (4, (5, nil)) in
            begin
              t[1] := nil;
              t
            end" "" "(4, nil)";
  t "tup3" "let t = (4, (5, nil)) in
            begin
              t[1] := t;
              t
            end" "" "(4, <cyclic tuple 1>)";
  t "tup4" "let t = (4, 6) in
            (t, t)"
           ""
           "((4, 6), (4, 6))"

]

(* let oom = [
 *   tgcerr "oomgc1" (7) "(1, (3, 4))" "" "Out of memory";
 *   tgc "oomgc2" (8) "(1, (3, 4))" "" "(1, (3, 4))";
 *   tvgc "oomgc3" (8) "(1, (3, 4))" "" "(1, (3, 4))";
 *   tgc "oomgc4" (4) "(3, 4)" "" "(3, 4)";
 * ] *)

let input = [
    t "input1" "let x = input() in x + 2" "123" "125"
  ]


let suite =
"suite">:::
 pair_tests @ input



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



(* ### Regression test suite (from Cobra) ### *)
let tests_from_cobra = [
  (* basic value reporting *)
  t "forty" forty "" "40";
  t "neg_fory" neg_forty "" "-40";
  t "fals" fals "" "false";
  t "tru" tru "" "true";
  t "max_snake_int" str_max_snake_num "" str_max_snake_num;
  t "min_snake_int" str_min_snake_num "" str_min_snake_num;
  terr "unbound_id" "v" "" "is not in scope";

  (* edge case tests for compile time integer overflow *)
  t "max_snake_num" str_max_snake_num "" str_max_snake_num;
  terr "overflow_max_snake_num_plus_one"
    str_max_snake_num_plus_one
    "" str_max_snake_num_plus_one;
  t "min_snake_num" str_min_snake_num "" str_min_snake_num;
  terr "underflow_min_snake_num_minus_one"
    str_min_snake_num_minus_one
    "" str_min_snake_num_minus_one;

  (* edge case tests for runtime integer overflow *)
  terr "add1_overflow" (sprintf "add1(%s)" str_max_snake_num) "" "overflow";
  terr "sub1_overflow" (sprintf "sub1(%s)" str_min_snake_num) "" "overflow";
  terr "sub_add_overflow"
    (sprintf "let x=sub1(%s) in add1(add1(x))" str_max_snake_num)
    "" "overflow";
  terr "overflow_in_value"
    (sprintf "let x=add1(%s) in 8" str_max_snake_num)
    "" "overflow";
  terr "overflow_in_plus"
    (sprintf "%s + 1" str_max_snake_num)
    "" "overflow";
  terr "overflow_in_plus_flipped"
    (sprintf "1 + %s" str_max_snake_num)
   ""  "overflow";
  terr "overflow_in_plus2"
    (sprintf "let x= 1 + %s in 98" str_max_snake_num)
    "" "overflow";
  terr "overflow_in_minus"
    (sprintf "print(0 - %s)" str_min_snake_num)
    "" "overflow";
  terr "overflow_in_times"
    (sprintf "2 * %s" str_max_snake_num)
    "" "overflow";
  terr "underflow_in_plus"
    (sprintf "let x= -1 + %s in 98" str_min_snake_num)
    "" "overflow";
  terr "underflow_in_minus"
    (sprintf "%s - 1" str_min_snake_num)
    "" "overflow";
  terr "underflow_in_times"
    (sprintf "2 * %s" str_min_snake_num)
    "" "overflow";

  (* isnum/isbool *)
  t "isnum1" "isnum(0)" "" "true";
  t "isnum2" "isnum(-2)" "" "true";
  t "isnum3" "isnum(9 + add1(2))" "" "true";
  t "isnum4" "isnum(true && false)" "" "false";
  t "isnum5" "isnum(true && true)" "" "false";
  t "isnum6" (sprintf "isnum(%s)" str_max_snake_num) "" "true";
  t "isnum7" (sprintf "isnum(%s)" str_min_snake_num) "" "true";
  t "isbool1" "isbool(true)" "" "true";
  t "isbool2" "isbool(false)"  "" "true";
  t "isbool3" "isbool(false || (add1(1) == 3))"  "" "true";
  t "isbool4" "isbool(isnum(7))"  "" "true";
  t "isbool5" "isbool(7)"  "" "false";
  t "isbool6" "isbool(0)"  "" "false";
  t "isbool7" "isbool(2 + 3)"  "" "false";
  t "isbool8" (sprintf "isbool(%s)" str_max_snake_num)  "" "false";
  t "isbool9" (sprintf "isbool(%s)" str_min_snake_num) ""  "false";

  (* print tests *)
  t "print_5" "print(5)"  "" "5\n5";
  t "print_-5" "print(-5)"  "" "-5\n-5";
  t "print_true" "print(true)"  "" "true\ntrue";
  t "print_false" "print(false)" ""  "false\nfalse";
  t "print_let_val" "let x=(print(6)) in 9" ""  "6\n9";
  t "nested_print_let_val"
      "let x = 1 in (let y = print(x + 1) in print(y + 2))"
       "" "2\n4\n4";
  t "print_mul" "print(7 * 9)"  "" "63\n63";
  t "print_nest" "print(print(1 + 2))"  "" "3\n3\n3";

  (* arithmetric tests *)
  t "plus" "4 + 9"  "" "13";
  t "minus" "4 - 9"  "" "-5";
  t "times" "4 * 9"  "" "36";
  t "add1" "add1(8)" ""  "9";
  t "sub1" "sub1(8)"  "" "7";
  t "plus_minus_times" "(add1(4) + 7) - sub1(3) * add1(2)" ""  "30";
  t "add_sub_edge" (sprintf "add1(sub1(%s)) + 0" str_max_snake_num)  "" str_max_snake_num;
  terr "plus_err" "4 + false"  "" "arithmetic expected a number";
  terr "minus_err" "(isnum(4) && false) - 9"  "" "arithmetic expected a number";
  terr "times_err" "4 * true"  "" "arithmetic expected a number";
  terr "add1_err" "add1(false || false)"  "" "arithmetic expected a number";
  terr "sub1_err" "sub1(false)"  "" "arithmetic expected a number";

  (* and tests *)
  t "and_ff" "false && false"  "" "false";
  t "and_ft" "false && true"  "" "false";
  t "and_tf" "true && false"  "" "false";
  t "and_tt" "true && true"  "" "true";
  t "and_side_effect" "true && print(true)"  "" "true\ntrue";
  terr "and_num" "true && 2"  "" "logic expected a boolean";
  terr "and_num2" "(true && true) && 3"  "" "logic expected a boolean";
  terr "and_num_flipped" "2 && true"  "" "logic expected a boolean";
  t "and_short_circuit" "false && print(2)"  "" "false";
  t "and_short_circuit1" "false && 8"  "" "false";

  (* or tests *)
  t "or_ff" "false || false" ""  "false";
  t "or_ft" "false || true" ""  "true";
  t "or_tf" "true || false"  "" "true";
  t "or_tt" "true || true" ""  "true";
  t "or_side_effects" "print(false) || print(true) && print(false)"  "" "false\ntrue\nfalse\nfalse";
  terr "or_num" "false || 8"  "" "logic expected a boolean";
  terr "or_num_flipped" "8 || false"  "" "logic expected a boolean";
  t "or_short_circuit_1" "true || 8" ""  "true";
  t "or_short_circuit_2" "true || print(2)"  "" "true";

  (* eq tests *)
  t "eq_1" "2 == 2"  "" "true";
  t "eq_2" "2 == 3"  "" "false";
  t "eq_3" "3 == 2"  "" "false";
  t "eq_4" "33 == 32"  "" "false";
  t "eq_5" "88 == 88"  "" "true";
  t "eq_6" "0 == false" ""  "false";
  t "eq_7" "true == 1" ""  "false";
  t "eq_8" "true == true" ""  "true";
  t "eq_9" "false == false" ""  "true";
  t "eq_10" "false == true" ""  "false";
  t "eq_11" "(-5 == -4) == !(3 == 3)" ""  "true";
  t "eq_12" "(-5 == -4) == (3 == 3)" ""  "false";

  (* greater tests *)
  t "greater_1" "2 > 2" ""  "false";
  t "greater_2" "2 > 3" ""  "false";
  t "greater_3" "3 > 2" ""  "true";
  t "greater_4" "33 > 32" ""  "true";
  t "greater_5" "88 > 88" ""  "false";
  terr "greater_er_1" "88 > true"  "" "comparison expected a number";
  terr "greater_er_2" "(1 == 1) > 2" ""  "comparison expected a number";

  (* greater eq tests *)
  t "greater_eq_1" "2 >= 2" ""  "true";
  t "greater_eq_2" "2 >= 3"  "" "false";
  t "greater_eq_3" "3 >= 2"  "" "true";
  t "greater_eq_4" "33 >= 32"  "" "true";
  t "greater_eq_5" "88 >= 88"  "" "true";
  terr "greater_eq_er_1" "88 > (9 == 8)"  "" "comparison expected a number";
  terr "greater_eq_er_2" "true > 2"  "" "comparison expected a number";

  (* less tests *)
  t "less_1" "2 < 2" "" "false";
  t "less_2" "2 < 3"  "" "true";
  t "less_3" "3 < 2"  "" "false";
  t "less_4" "33 < 32"  "" "false";
  t "less_5" "88 < 88"  "" "false";
  terr "less_er_1" "88 < (1 == 1)" ""  "comparison expected a number";
  terr "less_er_2" "(1 == -1) < 2" ""  "comparison expected a number";

  (* less eq tests *)
  t "less_eq_1" "2 <= 2" ""  "true";
  t "less_eq_2" "2 <= 3"  "" "true";
  t "less_eq_3" "3 <= 2"  "" "false";
  t "less_eq_4" "33 <= 32"  "" "false";
  t "less_eq_5" "88 <= 88"  "" "true";
  terr "less_eq_er_1" "88 <= (1 == 1)"  "" "comparison expected a number";
  terr "less_eq_er_2" "(1 == -1) <= 2"  "" "comparison expected a number";

  (* not tests *)
  t "not_t" "!(true)"  "" "false";
  t "not_f" "!(false)"  "" "true";
  t "not1" "!(2 == 3)" ""  "true";
  t "not2" "!(3 == 3)"  "" "false";
  t "not_let" "let x=true in !(x)"  "" "false";
  terr "not_err1" "!(1 + 2)" ""  "logic expected a boolean";

  (* if tests *)
  t "if_consts1" "if true: 5 else: 7"  "" "5";
  t "if_consts2" "if false: 5 else: 7"  "" "7";
  t "if_consts3" "if true: false else: true"  "" "false";
  t "if_consts4" "if false: false else: true"  "" "true";
  t "if_consts5" "if 2 < 3: add1(6 + 7) else: sub1(7 * 8)"  "" "14";
  t "if_mixed" "print(if 2 < 3: true else: 4)"  "" "true\ntrue";
  t "if_mixed2" "print(if 99 < 3: true else: 4)"  "" "4\n4";
  terr "if_cond_num_err" "if 1: true else: false"  "" "if expected a boolean";
  terr "if_binding_err" "if isnum(1): (let x=2 in x) else: x"  "" "is not in scope";

  (* if lazy eval tests *)
  t "if_lazy_consts1" "if true: 5 else: print(7)"  "" "5";
  t "if_lazy_consts2" "if false: print(5) else: 7" ""  "7";
  t "if_lazy_consts3" "if 2 < 3: add1(6 + 7) else: sub1(true)"  "" "14";
  t "if_lazy_consts4" "if 2 > 3: (true + true) else: sub1(7 * print(8))"  "" "8\n55";

  (* let tests *)
  t "let_const_num1" "let x=2,y=3 in x" ""  "2";
  t "let_const_num2" "let x=2,y=3 in 4" ""  "4";
  t "let_const_bool1" "let x=false,y=true in y"  "" "true";
  t "let_const_bool2" "let x=true in false"  "" "false";
  t "let_multi" "let x=2, y=add1(98), z=(100) in x + y + x"  "" "103";
  t "let_multi_bind_ref" "let x=3, y=add1(x), z=9*2*y in z" ""  "72";
  t "let_side_effect_unused" "let x=print(false) in 3"  "" "false\n3";  (* src: Piazza post #49 *)
  t "let_side_effect_used" "let x=print(isbool(6)) in x"  "" "false\nfalse";
  terr "let_unknown_var" "let x=1,s=2 in t"  "" "is not in scope";
  terr "let_backwards_binds" "let x=y,y=2 in 3"  "" "The identifier y, used at <let_backwards_binds, 1:6-1:7>, is not in scope";
  terr "let_bind_eval_first" "let x=true, y=add1(x) in x" ""  "arithmetic expected a number";
  t "shadow_across_lets_allowed" "let x = 4 in let x = 2 in x" ""  "2";
  terr "shadow_within_let_not_allowed_l" "let x = 4, x=2 in x" ""  "The identifier x, redefined at";
  terr "shadow_within_let_not_allowed_r" "let x = 4, x=2 in x" ""  ", duplicates one at";

  (* order ops tests *)
  t "order_ops1" "let z=true in isbool(1) || z"  "" "true";
  terr "order_op2" "(let z=true in isbool(1)) || z"  "" "is not in scope";

  (* PrintStack not yet implemented *)
  terr "print_stack" "printStack(2)" ""  "PrintStack not yet implemented";
]

let cobra_suite = "cobra_suite">:::tests_from_cobra


(* ### Regression test suite (from Diamondback) ### *)
let tests_from_diamondback = [
  (* ** Functions ** *)
  t "func_not_used_1" "def t(): true true"  "" "true";
  t "func_not_used_2" "def t(): true false"  "" "false";
  t "func_not_used_3" "def t(): 1 23"  "" "23";
  t "func_not_used_4" "def t(): if true: 88 else: 92 -3"  "" "-3";
  t "func_not_used_1a" "def id(x): x 10"  "" "10";
  t "func_not_used_2a" "def id(x): x true"  "" "true";
  t "func_not_used_3a" "def func(x): add1(x) true"  "" "true";
  t "func_not_used_4a" "def func(x): (2 + x) true"  "" "true";
  t "func_not_used_5a" "def func(x): if x<2: 0 else: 1 8"  "" "8";
  t "multiple_func_not_used" "def a(): 2 def ident(x): x def cat(x): print(x) 8"  "" "8";
  t "func_unused_args" "def fun(x, y, z): print(y) 8"  "" "8";

  (* Calling funcs *)
  t "basic_func_call" "def ident(x): x ident(10)"  "" "10";
  t "basic_func_call2" "def ident(x): x ident(false)"  "" "false";
  t "general_func_call" "def ident(x): x  11 * ident(print(7)+9)" ""  "7\n176";
  t "general_func_call2" "def add_eight(x): (x + (4 * add1(1))) def sub_seven(x): (x - 7)
                          if add_eight(2) < 10: print(false) else: add_eight(sub_seven(10))"
                           "" "11";
  t "general_func_call3a" "def ident(x): x  ident(let y=11 in y + 9)"  "" "20";
  t "general_func_call3b" "def ident(x): x  ident(let x=11 in x + 9)" ""  "20";
  t "general_func_call4" "def f(x): x  let x=6 in f(8)" ""  "8";
  t "noarg_func_call" "def f(): (let a=23,b=true in b) f()" ""  "true";

  t "fname_bind_in_body" "def fun(a,b,c): let fun=4 in add1(fun) \n fun(9,10,11)"  "" "5";
  t "func_split_env" "def f(x,y): let z = x * y in sub1(z)   let z = 9 in f(z, add1(z))" ""  "89";
  t "func_from_func" "def f(x,y): let z = x * y in z + z  def g(x): if isbool(x): 0 else: f(x,x) g(4)"  "" "32";
  t "func_from_func_backwards" "def f(): g()  def g(): sub1(2 * 8)  f()"  "" "15";
  t "max_tail_1" "def max(x,y): if x > y: x else: max(y,x) max(1,9)"  "" "9";
  t "max_tail_2" "def max(x,y): if x > y: x else: max(y,x) max(9,1)"  "" "9";
  t "rebind_arg" "def f(a,b): let a=b,b=8 in a+b f(4,10)"  "" "18";

  (* tail call testing *)
  t "tail_larger_arity_2_to_3" "def f(x,y): g(x,y,4)  def g(a,b,c): a - b + c  f(2,5)"  "" "1";
  t "tail_larger_arity_3_to_4" "def f(x,y,z): g(x,4,z,y)  def g(a,b,c,d): a - b + c - d  f(1,2,3)"  "" "-2";
  t "tail_larger_arity_2_to_4" "def f(x,y): g(x,-9, y,4)  def g(a,b,c,d): a - b + c - d  f(2,5)"  "" "12";
  t "tail_same_arity_1" "def f(x): g(x + 8)  def g(x): x - 2  f(4)"  "" "10";
  t "tail_same_arity_2" "def f(x,y): g(sub1(x),add1(y))  def g(x,y): x * y  f(3,5)"  "" "12";
  t "tail_same_arity_3" "def f(x,y,z): g(x,z,y)  def g(a,b,c): (a + b) * c  f(2,2,4)" ""  "12";
  t "tail_smaller_arity_3_to_2" "def f(i,j,k): g(i+j,k)  def g(i,k): i * k  f(0,2,2)" ""  "4";
  t "tail_smaller_arity_4_to_3" "def f(i,j,k,hi): g(i+j,k*hi,hi)  def g(i,k,x): x + (i*k)  f(0,2,2,1)"  "" "5";
  t "tail_smaller_arity_4_to_2" "def f(i,j,k,hi): g(i+j,k*hi)  def g(i,k): 3 + (i*k)  f(0,2,2,1)"  "" "7";

  (* Asserting that functions don't leak envs *)
  terr "func_split_env_err" "def f(x,y): let z = x * y in sub1(z)   let z = 9 in f(x, add1(z))"  "" "is not in scope";
  terr "func_split_env_err2a" "def f(x,y): let z = x * y in sub1(z)   let a = f(1, 2) in z"  "" "is not in scope";
  terr "func_split_env_err2b" "def f(x,y): let z = x * y in sub1(z)   let a = f(1, 2) in y" ""  "is not in scope";
  terr "func_split_env_err3" "def f(x,y): sub1(z)   let z=1 in f(1, 2)" ""  "is not in scope";
  terr "func_split_env_err4a" "def f(x,y): let z=99 in x+y  def g(x): print(z)   8"  "" "is not in scope";
  terr "func_split_env_err4b" "def f(x,y): let z=99 in x+y  def g(x): print(z)   let one=f(1,2) in g(3)"  "" "is not in scope";
  terr "func_split_env_err4c" "def f(x,y): let z=99 in x+y  z"  "" "is not in scope";
  terr "func_split_env_err4d" "def f(x,y): let z=99 in x+y  def g(w): print(x)   let one=f(1,2) in f(1,2)" ""  "is not in scope";

  (* Arity errors *)
  terr "arity_l" "def f(x): 2 f(4,5)"  "" "The function called at";
  terr "arity_r" "def f(x): 2 f(4,5)"  "" "expected an arity of 1, but received 2 arguments";
  terr "arity_err0" "def f(): (if isnum(12): 7 else: false)  f(4)"  "" "expected an arity of 0, but received 1 arguments";
  terr "arity_err1a" "def f(x): (if isnum(12): x else: false)  f()" ""  "expected an arity of 1, but received 0 arguments";
  terr "arity_err1b" "def f(x): (if isnum(12): x else: false)  f(4,8)"  "" "expected an arity of 1, but received 2 arguments";
  terr "arity_err2a" "def f(x,y): (if isnum(12): 7 else: false)  f(1)"  "" "expected an arity of 2, but received 1 arguments";
  terr "arity_err2b" "def f(x,y): (if isnum(12): 7 else: false)  f(1,3,4)"  "" "expected an arity of 2, but received 3 arguments";

  (* Name resolution for vars vs. funcs (vars shadow function names) *)
  terr "func_let_name" "def f(x,y): (if isnum(12): 7 else: false)  let f=99 in f(1,3)"  "" "is not in scope";
  terr "func_let_name2" "def f(x,y): (if isnum(12): 7 else: false)  let f=99 in f(1,3,4)"  "" "is not in scope";
  t "func_let_name3" "def f(x,y): (if isnum(12): 7 else: false)  let f=99 in add1(f)" ""  "100";

  (* UnboundFun errors *)
  terr "unbound_fun_l" "f()"  "" "The function name f, used at";
  terr "unbound_fun_r" "f()"  "" ", is not in scope";
  terr "unbound_fun" "def f(): add1(4 * 2)  def g(): sub1(2 * 8)  if false: h() else: 9" ""  "The function name h";
  terr "unbound_fun_in_decl" "def f(): add1(4 * 2)  def g(): h()  7"  "" "The function name h";
  terr "unbound_fun_let" "def f(): add1(4 * 2)  def g(): sub1(2 * 8) let h=true in h()"  "" "The function name h";

  (* UnboundId errors *)
  terr "unbound_id_l" "a"  "" "The identifier a, used at";
  terr "unbound_id_r" "a" ""  ", is not in scope";
  terr "unbound_id" "def id(y): y  let x=1 in y"  "" "is not in scope";
  terr "unbound_id_if" "if false: z else: 7" ""  "is not in scope";
  terr "unbound_arg" "def f(x, y): z  8"  "" "is not in scope";
  terr "unbound_arg2" "def f(x, y): x+y def g(a): z  8"  "" "is not in scope";
  terr "unbound_id_call" "def f(x, y): let z=y in add1(x + z)  isnum(f(3,a))"  "" "is not in scope";

  (* DuplicateId errors *)
  terr "duplicate_id_l" "let x=1,x=2 in 3" ""  "The identifier x, redefined at";
  terr "duplicate_id_r" "let x=1,x=2 in 3"  "" ", duplicates one at";

  (* DuplicateFun errors *)
  terr "duplicate_fun_l" "def f(): 2 def f(): 3 8"  "" "The function name f, redefined at";
  terr "duplicate_fun_r" "def f(): 2 def f(): 3 8"  "" ", duplicates one at";
  terr "duplicate_fun_2_l" "def f(a,b): 2 def f(): 3 8"  "" "The function name f, redefined at";
  terr "duplicate_fun_2_r" "def f(a,b): 2 def f(): 3 8"  "" ", duplicates one at";

  (* Overflow errors were tested in Cobra *)

  (* Multiple errors *)
  terr "unbound_duplicate_id_unbl" "let x=1,x=2 in y"  "" "The identifier y, used at";
  terr "unbound_duplicate_id_unbr" "let x=1,x=2 in y"  "" ", is not in scope";
  terr "unbound_duplicate_id_dupl" "let x=1,x=2 in y"  "" "The identifier x, redefined at";
  terr "unbound_duplicate_id_dupr" "let x=1,x=2 in y"  "" ", duplicates one at";

  terr "multi_errs_unbound_l" "def f(x, x): y  f(1)"  "" "The identifier y, used at ";
  terr "multi_errs_unbound_r" "def f(x, x): y  f(1)"  "" ", is not in scope";
  terr "multi_errs_duplicated_l" "def f(x, x): y  f(1)"  "" "The identifier x, redefined at ";
  terr "multi_errs_duplicated_r" "def f(x, x): y  f(1)"  "" ", duplicates one at ";
  terr "multi_errs_arity_mismatch_l" "def f(x, x): y  f(1)"  "" "The function called at ";
  terr "multi_errs_arity_mismatch_r" "def f(x, x): y  f(1)" ""  " expected an arity of 2, but received 1 arguments";
]

let tests_from_eggeater = [
  (* Tuples (nested) and outputs *)
  t "0tup" "()" "" "()";
  t "1tup_1" "(6,)" "" "(6,)";
  t "1tup_2" "(false,)" "" "(false,)";
  t "pair_1" "(1,2)" "" "(1,2)";
  t "pair_2" "(1,(true,8))" "" "(1,(true,8))";
  t "trip_1" "(true,false,7)" "" "(true,false,7)";
  t "trip_2" "(true,(),7)" "" "(true,(),7)";
  t "trip_3" "((16,),(),7)" "" "((16,),(),7)";
  t "trip_4" "((16,),(),(true,18,20))" "" "((16,),(),(true,18,20))";

  (* Tuples in unary ops *)
  terr "tup_add1" "let var=(1,) in add1(var)" "" "arithmetic expected a number";
  terr "tup_sub1" "let var=(1,3) in sub1(var)" "" "arithmetic expected a number";
  t "tup_print" "let var=print((1,)) in print(var)" "" "(1,)\n(1,)\n(1,)";
  t "tup_type_checks"
    "let var=(1,) in (if isbool(var): -9 else: (if isnum(var): -8 else: istuple(var)))"
    "" "true";
  terr "tup_not" "!((true,))" "" "logic expected a boolean";

  (* Tuples in binary ops *)
  terr "tup_plus_num" "let var=(1,2) in var + 3" "" "arithmetic expected a number";
  terr "tup_plus_num2" "let var=(1,2) in 3 + var" "" "arithmetic expected a number";
  terr "tup_plus_tup" "(1,) + (3,)" "" "arithmetic expected a number";
  terr "tup_plus_tup2" "(1,3) + (3,1)" "" "arithmetic expected a number";
  terr "tup_minus_num" "1 - (if true: (1,1) else: (2,2))" "" "arithmetic expected a number";
  terr "tup_minus_tup" "(1,) - (3,)" "" "arithmetic expected a number";
  terr "tup_times_num" "let var=(1,2) in var * 3" "" "arithmetic expected a number";
  terr "tup_times_tup" "(1,34) * (3,2)" "" "arithmetic expected a number";

  terr "tup_and_bool" "let var=(1,2) in var && true" "" "logic expected a boolean";
  terr "tup_and_bool2" "let var=(1,2) in true && var" "" "logic expected a boolean";
  terr "tup_and_bool3" "let var=(true,) in var && true" "" "logic expected a boolean";
  t "tup_and_bool_shortcircuit" "false && (true,)" "" "false";
  terr "tup_and_tup" "let var=(true,) in var && (true,)" "" "logic expected a boolean";

  terr "tup_or_bool" "let var=(1,2) in var || true" "" "logic expected a boolean";
  terr "tup_or_bool2" "let var=(1,2) in false || var" "" "logic expected a boolean";
  terr "tup_or_bool3" "let var=(true,) in var || true" "" "logic expected a boolean";
  t "tup_or_bool_shortcircuit" "true || (false,)" "" "true";
  terr "tup_or_tup" "let var=(false,) in var || (false,)" "" "logic expected a boolean";

  terr "tup_gt_tup" "(1,) > 2" "" "comparison expected a number";
  terr "tup_ge_tup" "(1,2) >= 2" "" "comparison expected a number";
  terr "tup_lt_tup" "(9,) < 2" "" "comparison expected a number";
  terr "tup_le_tup" "9 < (1,2)" "" "comparison expected a number";

  t "tup_eq_self" "let t=(1,2,true,(3,4)) in t == t" "" "true";
  t "tup_eq_copy" "let t=(1,2,3,4), t2=t in t == t2" "" "true";
  t "tup_eq_dupl" "(1,) == (1,)" "" "false";
  t "tup_eq_dupl2" "let t=(1,2,3,4), t2=(1,2,3,4) in t == t2" "" "false";
  t "tup_eq_num" "let t=5 in (t,) == t" "" "false";
  t "tup_eq_bool" "let t=true in (t,) == t" "" "false";

  (* GetItem *)
  t "get_item_0" "(false,)[0]" "" "false";
  t "get_item_1" "(1,2)[0]" "" "1";
  t "get_item_2" "(1,2)[1]" "" "2";
  t "get_item_3" "(1,2,3,4,5,6)[0]" "" "1";
  t "get_item_4" "(1,2,3,4,5,6)[1]" "" "2";
  t "get_item_5" "(1,2,3,4,5,6)[3]" "" "4";
  t "get_item_6" "(1,2,3,4,5,6)[5]" "" "6";
  t "get_item_7" "let t=5 in (t,)[0] == t" "" "true";
  terr "get_from_num" "7[0]" "" "expected tuple";
  terr "get_from_bool" "false[0]" "" "expected tuple";
  terr "get_neg_idx" "(1,2)[-1]" "" "index too small";
  terr "get_big_idx0" "()[0]" "" "index too big";
  terr "get_big_idx1" "(1,)[1]" "" "index too big";
  terr "get_big_idx1" "(1,2)[2]" "" "index too big";

  (* SetItem *)
  t "set_item_0" "(1,)[0] := 6" "" "(6,)";
  t "set_item_1" "(1,2)[1] := 6" "" "(1,6)";
  t "set_item_2" "(1,2)[1] := false" "" "(1,false)";
  t "set_item_3" "(1,2,true,false)[0] := false" "" "(false,2,true,false)";
  t "set_item_4" "(1,2,(8,7),false)[2] := (20,5,6)" "" "(1,2,(20,5,6),false)";
  t "set_item_5" "((true,9),2,(8,7),false)[2] := (20,5,6)" "" "((true,9),2,(20,5,6),false)";
  terr "set_from_num" "7[0]:=true" "" "expected tuple";
  terr "set_from_bool" "false[0]:=false" "" "expected tuple";
  terr "get_neg_idx" "(1,2)[-1]:=3" "" "index too small";
  terr "get_big_idx0" "()[0]:=2" "" "index too big";
  terr "get_big_idx1" "(1,)[1]:=2" "" "index too big";
  terr "get_big_idx2" "(1,2)[2]:=9" "" "index too big";

  (* Tuples and lets *)
  t "tup_let_1" "let (a,b) = (5,4) in a - b" "" "1";
  t "tup_let_2" "let ((a,b),_,(x,y,z)) = ((5,4),print(-99),(1,2,3)) in (a*b) - (x*y*z)" "" "-99\n14";
  t "tup_let_3" "let t=(print(1),print((2,3))) in print(t)" "" "1\n(2,3)\n(1,(2,3))\n(1,(2,3))";
  t "tup_let_4"
    "let (i0, i1, _, i3) = ((let i0=false in !(i0)), (9,), 4, 3) in (if i0: i1[0] * 4 - 3 else: -99)"
    "" "33";

  (* Lets and blanks *)
  t "lets_and_blanks" "let _=2 in 3" "" "3";
  t "lets_and_blanks2" "let _=print(1) in 2" "" "1\n2";
  t "lets_and_multiple_blanks"
    "let _=print(1), _=print(false), _=((print((-3,)),), print(4)) in true"
    "" "1\nfalse\n(-3,)\n4\ntrue";

  (* nil tests *)
  t "print_nil" "let x=nil in print(x)" "" "nil";
  t "print_tip_of_nil" "let x=nil in print((x,))" "" "TODO?";
  terr "get_nil" "nil[0]" "" "access component of nil";
  terr "set_nil" "nil[0]:=true" "" "access component of nil";
  terr "set_nil" "let x=nil in (x[0]:=true)" "" "access component of nil";

(* (a,b,(c,d,e),f) = (1,2,(3,3),4) should be error *)


]

let diamondback_suite = "diamondback_suite">:::tests_from_diamondback

let eggeater_suite = "eggeater_suite">:::tests_from_eggeater


let () =
  run_test_tt_main ("all_tests">:::[(*cobra_suite diamondback_suite *) eggeater_suite (*suite; input_file_test_suite ()*)])
;;

