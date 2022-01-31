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
  t "neg_forty_one" "-41" "-41";
  (* todo add test(s) about boolean here *)
  
  (* Add1 / Sub1 *)
  t "add1" "(add1 4)" "5";
  t "sub1" "(sub1 4)" "3";
  t "sub_add" "(add1 (sub1 44))" "44";
  t "add_sub" "(sub1 (add1 40))" "40";
  t "add_add" "(add1 (add1 111))" "113";
  t "sub_sub" "(sub1 (sub1 1000))" "998";

  (* Add1 / Sub1 Errors *)
  te "add1_multi" "(add1 2 4)" "todo"; (* todo should perhaps handle this error case better *)
  te "sub1_multi" "(sub1 2 4)" "todo"; (* todo should perhaps handle this error case better *)


  (* Let bindings correct *)
  t "let" "(let ((x 10)) x)" "10";
  t "let_const" "(let ((a 7)) 71)" "71";
  t "let_var" "(let ((a 7)) (add1 a))" "8";
  te "let_unbound" "(let ((nota 8)) myvar)" "Unbound symbol: myvar";
  t "let_var_name_with_num" "(let ((apple87 7)) (add1 apple87))" "8";
  t "let_multi_bindings_m" "(let ((m 11) (n 22) (o 33) (p 44) (q 55) (r 66) (s 77)) m)" "11";
  t "let_multi_bindings_q" "(let ((m 11) (n 22) (o 33) (p 44) (q 55) (r 66) (s 77)) q)" "55";
  t "let_multi_bindings_s" "(let ((m 11) (n 22) (o 33) (p 44) (q 55) (r 66) (s 77)) s)" "77";
  t "let_complex_bind" "(let ((a 4) (b (add1 (sub1 (add1 2))))) b)" "3";
  t "let_nested_bind_easy" "(let ((g -99) (h g)) h)" "-99";
  t "let_nested_bind" "(let ((g -99) (h (add1 g))) h)" "-98";
  t "let_nested_bind_multi" "(let ((g -99) (h g) (i h) (final (add1 i))) final)" "-98";
  t "let_nested_bind_let" "(let ((orig 2) (outer (let ((mid (let ((inner orig)) inner))) mid))) outer)" "2";
  t "nested_let_a" "(let ((a 1) (b 2)) (let ((c 3)) (let ((d 4) (e 5)) a)))" "1";
  t "nested_let_b" "(let ((a 1) (b 2)) (let ((c 3)) (let ((d 4) (e 5)) b)))" "2";
  t "nested_let_c" "(let ((a 1) (b 2)) (let ((c 3)) (let ((d 4) (e 5)) c)))" "3";
  t "nested_let_d" "(let ((a 1) (b 2)) (let ((c 3)) (let ((d 4) (e 5)) d)))" "4";
  t "nested_let_e" "(let ((a 1) (b 2)) (let ((c 3)) (let ((d 4) (e 5)) e)))" "5";
  t "nested_let_in_binds" "(let ((x (let ((inner 8) (inner2 10))
                                         (add1 inner))) (outer 100))
                                x)" "9";
  t "nested_let_in_binds2" "(let ((x (let ((inner 8) (inner2 10))
                                         (add1 inner))) (outer 100))
                                outer)" "100";
  t "double_nested_let_in_binds" "(let ((x (let ((inner 8)
                                                 (inner2 (let ((innerinner 1000)) (sub1 innerinner))))
                                              (add1 inner2)))
                                        (outer 100))
                                      x)" "1000";
  
  (* Let bindings errors *)
  te "nested_let_in_binds_err" "(let ((x (let ((inner 8) (inner2 10))
                                         (add1 inner))) (outer 100))
                                inner)" "Unbound symbol: inner";
  te "nested_let_in_binds_err2" "(let ((x (let ((inner 8) (inner2 10))
                                         (add1 inner))) (outer 100))
                                inner2)" "Unbound symbol: inner2";
  te "double_nested_let_in_binds_err" "(let ((x (let ((inner 8)
                                                 (inner2 (let ((innerinner 1000)) (sub1 innerinner))))
                                              (add1 inner2)))
                                        (outer 100))
                                      innerinner)" "Unbound symbol: innerinner";
  te "let_empty" "(let (()) 2)" "expected list of bindings";
  te "let_bind_num" "(let ((3)) 3)" "Syntax error in let-bindings";
  te "let_rebind_num" "(let ((3 4)) 3)" "Syntax error in let-bindings";
  te "let_no_binding_list" "(let (x 10) x)" "expected list of bindings";
  te "let_dup_binds" "(let ((x 1) (x 1)) 2)" "Duplicate symbol x";
  te "let_dup_binds2" "(let ((x 1) (x 3)) 2)" "Duplicate symbol x";
  te "let_dup_binds3" "(let ((x 1) (y 9) (x 1)) 2)" "Duplicate symbol x";
  te "let_dup_binds4" "(let ((x 1) (y 9) (z 33) (x 3)) 2)" "Duplicate symbol x";
  te "let_malformed_list" "(let ((a 1 b 2 c 3)) 2)" "expected list of bindings";


  (* todo should these (next 3 tests) be allowed? seems like no but currently they pass *)
  t "let_rebind_add1" "(let ((add1 4)) 5)" "5";
  t "let_rebind_add1_used" "(let ((add1 4)) add1)" "4";
  t "let_rebind_add1_used2" "(let ((add1 4)) (add1 add1))" "5";

  (* Parentheses are not "free" *)
  te "invalid_parens_empty" "()" "paren must be followed by let, add, or sub";
  te "invalid_parens_num" "(1)" "paren must be followed by let, add, or sub";
  te "invalid_parens_num2" "(let ((a (2))) a)" "paren must be followed by let, add, or sub";
  te "invalid_parens_num3" "(let ((a 2)) (a))" "paren must be followed by let, add, or sub";
  te "invalid_parens_num4" "(add1 (2))" "paren must be followed by let, add, or sub";


  te "unknown_keyword" "(word ((x 1)) x)" "paren must be followed by let, add, or sub";
  te "unknown_keyword_nested" "(let ((x 1)) (let ((y 1)) (add1 (blah y))))" "paren must be followed by let, add, or sub";
  te "unknown_keyword_nested2" "(let ((x 1)) (let ((y (bloh 2))) (add1 x)))" "paren must be followed by let, add, or sub";

  (* todo- use funcs ti and tie to test the input files we have, and add more such files *)
  ]
;;


let () =
  run_test_tt_main suite
;;
