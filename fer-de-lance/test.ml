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

let tparse name program expected = name>::fun _ ->
  assert_equal (untagP expected) (untagP (parse_string name program)) ~printer:string_of_program;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

let tfvs name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    match anfed with
    | AProgram(body, _) ->
      let vars = free_vars body in
      let c = Stdlib.compare in
      let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in
      assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print)
;;


(* Provided with this assignment
let forty_one = "41";;

let forty_one_a = (AProgram(ACExpr(CImmExpr(ImmNum(41L, ()))), ()))

let test_prog = "let x = if sub1(55) < 54: (if 1 > 0: add1(2) else: add1(3)) else: (if 0 == 0: sub1(4) else: sub1(5)) in x"
let anf1 = (anf     (tag (parse_string "test" test_prog)))

let suite =
  "suite">:::
    [

      t "test_is_bool1" "isbool(true)" "" "true";
      t "test_is_bool2" "isbool(false)" "" "true";
      t "test_is_bool3" "isbool(0)" "" "false";
      t "test_is_bool4" "isbool(123)" "" "false";
      t "test_is_bool5" "isbool((0,123))" "" "false";
      t "test_is_bool6" "isbool((true,123))" "" "false";
      t "test_is_bool7" "isbool((123,123))" "" "false";
      t "test_is_bool8" "isbool((false,123))" "" "false";

      t "test_is_tuple1" "istuple(true)" "" "false";
      t "test_is_tuple2" "istuple(false)" "" "false";
      t "test_is_tuple3" "istuple(0)" "" "false";
      t "test_is_tuple4" "istuple(123)" "" "false";
      t "test_is_tuple5" "istuple((0,123))" "" "true";
      t "test_is_tuple6" "istuple((true,123))" "" "true";
      t "test_is_tuple7" "istuple((123,123))" "" "true";
      t "test_is_tuple8" "istuple((false,123))" "" "true";

      t "test_is_num1" "isnum(true)" "" "false";
      t "test_is_num2" "isnum(false)" "" "false";
      t "test_is_num3" "isnum(0)" "" "true";
      t "test_is_num4" "isnum(123)" "" "true";
      t "test_is_num5" "isnum((0,123))" "" "false";
      t "test_is_num6" "isnum((true,123))" "" "false";
      t "test_is_num7" "isnum((123,123))" "" "false";
      t "test_is_num8" "isnum((false,123))" "" "false";

      tanf "forty_one_anf"
        (Program([], ENumber(41L, ()), ()))
        "" 
        forty_one_a;

      terr "scope_err1" "let x = true in (let y = (let x = false in x) in y)" "" "shadows one defined";

      ta "forty_one_run_anf" ((atag forty_one_a), []) "" "41";
      
      t "forty_one" forty_one "" "41";


      t "test" test_prog "" "3";
      
      (* Some useful if tests to start you off *)

      t "if1" "if 7 < 8: 5 else: 3" "" "5";
      t "if2" "if 0 > 1: 4 else: 2" "" "2";

      terr "overflow" "add1(5073741823000000000)" "" "overflow";

      (* tvg "funcalls" "def fact(n): if n < 2: 1 else: n * fact(n - 1)\n\nfact(5)" "" "120" *)
          
    ]
;;
*)


(* ### Regression test suite (from Cobra) ### *)
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



let () =
  run_test_tt_main ("all_tests">:::[cobra_suite; input_file_test_suite ()])
;;
