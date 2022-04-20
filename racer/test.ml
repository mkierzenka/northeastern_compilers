open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors
open Anf
open Util

let t name program input expected = name>::test_run ~args:[] ~std_input:input Naive program name expected;;
let tr name program input expected = name>::test_run ~args:[] ~std_input:input Register program name expected;;
let ta name program input expected = name>::test_run_anf ~args:[] ~std_input:input program name expected;;
let tgc name heap_size program input expected = name>::test_run ~args:[string_of_int heap_size] ~std_input:input Naive program name expected;;
let tvg name program input expected = name>::test_run_valgrind ~args:[] ~std_input:input Naive program name expected;;
let tvgc name heap_size program input expected = name>::test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input Naive program name expected;;
let terr name program input expected = name>::test_err ~args:[] ~std_input:input Naive program name expected;;
let tgcerr name heap_size program input expected = name>::test_err ~args:[string_of_int heap_size] ~std_input:input Naive program name expected;;
let tanf name program input expected = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

let tparse name program expected = name>::fun _ ->
  assert_equal (untagP expected) (untagP (parse_string name program)) ~printer:string_of_program;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

(* let tfvs name program expected = name>:: *)
(*   (fun _ -> *)
(*     let ast = parse_string name program in *)
(*     let anfed = anf (tag ast) in *)
(*     let vars = free_vars_P anfed [] in *)
(*     let c = Stdlib.compare in *)
(*     let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in *)
(*     assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print) *)
(* ;; *)

let tfvs name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    let fv_prog = free_vars_cache anfed in
    assert_equal expected (string_of_aprogram_with_fvs fv_prog) ~printer:(fun s -> s))

let builtins_size = 4 (* arity + 0 vars + codeptr + padding *) * 1 (* TODO FIXME (List.length Compile.native_fun_bindings) *)

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

let oom = [
  tgcerr "oomgc1" (7 + builtins_size) "(1, (3, 4))" "" "Out of memory";
  tgc "oomgc2" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
  tvgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
  tgc "oomgc4" (4 + builtins_size) "(3, 4)" "" "(3, 4)";
  tgcerr "oomgc5" (3 + builtins_size) "(1, 2, 3, 4, 5, 6, 7, 8, 9, 0)" "" "Allocation";
]

let gc = [
  tgc "gc_lam1" (10 + builtins_size)
      "let f = (lambda: (1, 2)) in
       begin
         f();
         f();
         f();
         f()
       end"
      ""
      "(1, 2)";
]

let input = [
  t "input1" "let x = input() in x + 2" "123" "125";
  t "rename_input" "let new_input = input in new_input()" "1337" "1337";
]

let racer = [
  t "let_a" "let a = 3 in a" "" "3";

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

  terr "fname_bind_in_body" "def fun(a,b,c): let fun=4 in add1(fun) \n fun(9,10,11)"  "" "shadows";
  t "func_split_env" "def f(x,y): let z = x * y in sub1(z)   let z = 9 in f(z, add1(z))" ""  "89";
  t "func_from_func" "def f(x,y): let z = x * y in z + z  and def g(x): if isbool(x): 0 else: f(x,x) g(4)"  "" "32";
  terr "func_from_nonpreceding_func_dif_grp" "def g(x): if isbool(x): 0 else: f(x,x)  def f(x,y): let z = x * y in z + z g(4)"  "" "The identifier f";
  t "func_from_func_backwards" "def f(): g()  and def g(): sub1(2 * 8)  f()"  "" "15";
  terr "func_from_func_backwards_dif_grp" "def f(): g()  def g(): sub1(2 * 8)  f()"  "" "The identifier g";
  
  t "max_tail_1" "def max(x,y): if x > y: x else: max(y,x) max(1,9)"  "" "9";
  t "max_tail_2" "def max(x,y): if x > y: x else: max(y,x) max(9,1)"  "" "9";
  terr "rebind_arg" "def f(a,b): let a=b,b=8 in a+b f(4,10)"  "" "shadows";

  t "lambda_seq_left" "(lambda(x): x + 5);8" "" "8";
  t "lambda_seq_right" "8;(lambda(x): x + 5)" "" "11";
]

let fvs_tests = [
  tfvs "fvs_binop1" "4 + b" "(4{} + b{b; }){b; }\n{b; }";
  tfvs "fvs_binop2" "b + 4" "(b{b; } + 4{}){b; }\n{b; }";
  tfvs "fvs_binop3" "b + b" "(b{b; } + b{b; }){b; }\n{b; }";
  tfvs "fvs_binop4" "4 + 6" "(4{} + 6{}){}\n{}";
  tfvs "fvs_id" "b" "b{b; }\n{b; }";
  tfvs "fvs_if1" "if b: 4 else: 5" "(if b{b; }: 4{} else: 5{}){b; }\n{b; }";
  tfvs "fvs_if2" "if b: c else: d" "(if b{b; }: c{c; } else: d{d; }){d; c; b; }\n{d; c; b; }";
  tfvs "fvs_if3" "if false: a else: b" "(if false{}: a{a; } else: b{b; }){b; a; }\n{b; a; }";
  tfvs "fvs_let" "let a = c in b + a" "(alet a = c{c; } in (b{b; } + a{}){b; }){c; b; }\n{c; b; }";
  tfvs "fvs_letrec" "let rec func = (lambda(x,y): if x < a: y else: let tmp = b in tmp * y) in func(1, 2)"
                    "(aletrec func = (lam(x, y) (alet binop_7 = (x{} < a{a; }){a; } in (if binop_7{}: y{} else: (alet tmp = b{b; } in (tmp{} * y{}){}){b; }){b; }){b; a; }){b; a; } in (?func{}(1{}, 2{})){}){b; a; }\n{b; a; }";
]

let racer_tr = [
  tr "reg_let1" "let a = input(), b=4*5 in (if a > b: false else: a + a)" "444" "false";
]

let suite =
"unit_tests">:::
  pair_tests @ oom @ gc @ input @ racer @ fvs_tests @ racer_tr



let () =
  run_test_tt_main ("all_tests">:::[suite; input_file_test_suite ()])
;;
