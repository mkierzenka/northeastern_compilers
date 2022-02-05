open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Str


let tag_of_string = string_of_int;;

let ast_of_tag_expr (e : tag expr) : string =
  format_expr e tag_of_string
;;

(* removes whitespace from a string *)
let remove_ws (s : string) : string =
  global_replace (regexp "[\n\t ]") "" s

(* testing infrastructure specifically for check_scope *)
let tcheck_scope_run ?args:(args=[]) ?std_input:(std_input="") program name test_ctxt =
  let prog = parse_string name program in
  check_scope prog;
  assert true

let tcheck_scope (name : string) (program : string) : OUnit2.test =
  name>::tcheck_scope_run program name;;
;;

(* testing infrastructure specifically for tag *)
let ttag_run ?args:(args=[]) ?std_input:(std_input="") program name expected test_ctxt =
  let prog = parse_string name program in
  check_scope prog;
  let tagged : tag expr = tag prog in
  assert_equal (Ok(remove_ws expected)) (Ok(remove_ws (ast_of_tag_expr tagged))) ~printer:result_printer

let ttag (name : string) (program : string) (expected : string) : OUnit2.test =
  name>::ttag_run program name expected;;
;;

(* testing infrastructure specifically for rename *)
let trename_run ?args:(args=[]) ?std_input:(std_input="") program name expected test_ctxt =
  let prog = parse_string name program in
  check_scope prog;
  let tagged : tag expr = tag prog in
  let renamed : tag expr = rename tagged in
  assert_equal (Ok(remove_ws expected)) (Ok(remove_ws (ast_of_tag_expr renamed))) ~printer:result_printer

let trename (name : string) (program : string) (expected : string) : OUnit2.test =
  name>::trename_run program name expected;;
;;


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

let forty_one = "41";;

let forty_one_a = (ENumber(41L, ()))

let check_scope_suite =
"check_scope_suite">:::
 [
   tcheck_scope "check_scope1" "8";
   tcheck_scope "check_scope2" "(8)";

   tcheck_scope "check_scope3" "add1(8)";
   tcheck_scope "check_scope4" "8 * 2";
   tcheck_scope "check_scope5" "8 * 2 + 2";
   tcheck_scope "check_scope6" "sub1((1 * 2) + 3) + 4";

   (* if *)
   tcheck_scope "check_scope7" "if 0: 1 else: 2";
   tcheck_scope "check_scope8" "if 1: 1 else: 2";
   tcheck_scope "check_scope9" "if (let x=1 in x): 1 else: 2";
   tcheck_scope "check_scope10" "if 0: (let x=1 in x) else: 2";
   tcheck_scope "check_scope11" "if 0: 1 else: (let x=1 in x)";
   tcheck_scope "check_scope12" "if 1: (let x=1 in x) else: 2";
   tcheck_scope "check_scope13" "if 1: 1 else: (let x=1 in x)";

   (* let *)
   tcheck_scope "check_scope14" "let x=9 in x";
   tcheck_scope "check_scope15" "let x=9 in add1(x)";
   tcheck_scope "check_scope16" "let x=9,y=77 in add1(x)";
   tcheck_scope "check_scope17" "let y=9,x=77 in add1(x)";
   tcheck_scope "check_scope18" "let y=9,x=y in x";
        (* nested *)
   tcheck_scope "check_scope19" "let y=9,x=77 in (let a=1,b=2,c=3 in x)";
   tcheck_scope "check_scope20" "let y=9,x=77 in (let a=1,b=2,c=3 in y)";
   tcheck_scope "check_scope21" "let y=9,x=77 in (let a=1,b=2,c=3 in c)";
   tcheck_scope "check_scope22" "let y=9,x=(let a=1,b=2,c=3 in y) in x";
   tcheck_scope "check_scope23" "let y=9,x=(let a=1,b=2,c=3 in b) in x";
   tcheck_scope "check_scope24" "let y=9,x=(let a=1,b=2,c=3 in y) in x";
        (* nested if *)
   tcheck_scope "check_scope25" "let x=4 in if 0: 1 else: 2";
   tcheck_scope "check_scope26" "let x=4 in if 1: 1 else: 2";
   tcheck_scope "check_scope27" "let x=4 in if x: 1 else: 2";
   tcheck_scope "check_scope28" "let x=4 in if 0: x else: 2";
   tcheck_scope "check_scope29" "let x=4 in if 0: 1 else: x";
   tcheck_scope "check_scope30" "let x=4 in if 1: x else: 2";
   tcheck_scope "check_scope31" "let x=4 in if 1: 1 else: x";
(* todo add more tests here? *)

   (* ERRORS *)
   te "check_scope_err1" "x" "Unbound symbol x";
   te "check_scope_err2" "add1(x)" "Unbound symbol x";
   te "check_scope_err3" "x * 2" "Unbound symbol x";
   te "check_scope_err4" "8 * x" "Unbound symbol x";

   (* if *)
   te "check_scope_err5" "if x: 1 else: 2" "Unbound symbol x";
   te "check_scope_err6" "if 0: x else: 2" "Unbound symbol x";
   te "check_scope_err7" "if 0: 1 else: x" "Unbound symbol x";
   te "check_scope_err8" "if 1: x else: 2" "Unbound symbol x";
   te "check_scope_err9" "if 1: 1 else: x" "Unbound symbol x";
        (* nested let*)
   te "check_scope_err10" "if (let x=1 in 0): 1 else: x" "Unbound symbol x";
   te "check_scope_err11" "if (let x=1 in 0): x else: 1" "Unbound symbol x";
   te "check_scope_err12" "if (let x=1 in 1): x else: 1" "Unbound symbol x";
   te "check_scope_err13" "if (let x=1 in 1): 1 else: x" "Unbound symbol x";
   te "check_scope_err14" "if (let x=1 in 0): 1 else: x" "Unbound symbol x";
   te "check_scope_err15" "if (let x=1 in 0): 1 else: x" "Unbound symbol x";
   te "check_scope_err16" "if (let x=1 in 0): 1 else: x" "Unbound symbol x";

   (* let *)
   te "check_scope_err17" "let x=9 in y" "Unbound symbol y";
   te "check_scope_err18" "let x=9 in add1(y)" "Unbound symbol y";
   te "check_scope_err19" "let x=9,z=33 in add1(y)" "Unbound symbol y";

(* todo add more tests here? *)
 ]
;;


let tag_suite =
"tag_suite">:::
 [
   ttag "tag1" "8" "ENumber<0>(8)";
   ttag "tag2" "add1(8)" "EPrim1<1>(Add1, ENumber<0>(8))";
   ttag "tag3" "let x=9 in x" "ELet<3>((( \"x\"<1>, ENumber<0>(9))), EId<2>(\"x\"))";
   ttag "tag4" "let x=9,y=55 in x" "ELet<5>((( \"x\"<1>, ENumber<0>(9)), ( \"y\"<3>, ENumber<2>(55))), EId<4>(\"x\"))";
   ttag "tag5" "let x=9,y=55 in y" "ELet<5>((( \"x\"<1>, ENumber<0>(9)), ( \"y\"<3>, ENumber<2>(55))), EId<4>(\"y\"))";

 ]
;;


let suite =
"suite">:::
 [

  tanf "forty_one_anf"
       (ENumber(41L, ()))
       forty_one_a;

  (* For CS4410 students, with unnecessary let-bindings *)
  tanf "prim1_anf_4410"
       (EPrim1(Sub1, ENumber(55L, ()), ()))
       (ELet(["unary_1", EPrim1(Sub1, ENumber(55L, ()), ()), ()],
             EId("unary_1", ()),
             ()));

  (* For CS6410 students, with optimized let-bindings *)
  tanf "prim1_anf_6410"
       (EPrim1(Sub1, ENumber(55L, ()), ()))
       (EPrim1(Sub1, ENumber(55L, ()), ()));

  ta "forty_one_run_anf" (tag forty_one_a) "41";
 
  t "forty_one" forty_one "41";


  tprog "test1.boa" "3";
      
    (* Some useful if tests to start you off *)

  t "if1" "if 5: 4 else: 2" "4";
  t "if2" "if 0: 4 else: 2" "2";

  ]
;;


let () =
  run_test_tt_main check_scope_suite;
  run_test_tt_main tag_suite;
  (* run_test_tt_main suite *)
;;
