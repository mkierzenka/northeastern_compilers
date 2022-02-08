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

let tanf_4410 (name : string) (program : 'a expr) (expected : unit expr) = name>::fun _ ->
  assert_equal expected (anf_4410 (tag program)) ~printer:string_of_expr;;

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
        (* shadowing *)
   tcheck_scope "check_scope25" "let x=9,y=55 in (let x=2 in x)";
        (* nested if *)
   tcheck_scope "check_scope26" "let x=4 in if 0: 1 else: 2";
   tcheck_scope "check_scope27" "let x=4 in if 1: 1 else: 2";
   tcheck_scope "check_scope28" "let x=4 in if x: 1 else: 2";
   tcheck_scope "check_scope29" "let x=4 in if 0: x else: 2";
   tcheck_scope "check_scope30" "let x=4 in if 0: 1 else: x";
   tcheck_scope "check_scope31" "let x=4 in if 1: x else: 2";
   tcheck_scope "check_scope32" "let x=4 in if 1: 1 else: x";


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
 ]
;;


let tag_suite =
"tag_suite">:::
 [
   ttag "tag1" "8" "ENumber<0>(8)";
   ttag "tag1" "(8)" "ENumber<0>(8)";
   ttag "tag2" "add1(8)" "EPrim1<1>(Add1, ENumber<0>(8))";
   ttag "tag2" "sub1(8)" "EPrim1<1>(Sub1, ENumber<0>(8))";
   ttag "tag2" "4 + 5" "EPrim2<2>(Plus, ENumber<0>(4), ENumber<1>(5))";
   ttag "tag2" "4 - 5" "EPrim2<2>(Minus, ENumber<0>(4), ENumber<1>(5))";
   ttag "tag2" "4 * 5" "EPrim2<2>(Times, ENumber<0>(4), ENumber<1>(5))";
   ttag "tag2" "4 + (5 * 7)" "EPrim2<4>(Plus, ENumber<0>(4), EPrim2<3>(Times, ENumber<1>(5), ENumber<2>(7)))";

   (* if *)
   ttag "tag2" "if 6: 7 else: 8" "EIf<3>(ENumber<0>(6), ENumber<1>(7), ENumber<2>(8))";
   ttag "tag2" "if 6: 4 + 5 else: 8 + 9" "EIf<7>(ENumber<0>(6), EPrim2<3>(Plus, ENumber<1>(4), ENumber<2>(5)), EPrim2<6>(Plus, ENumber<4>(8), ENumber<5>(9)))";

   (* let *)
   ttag "tag3" "let x=9 in x" "ELet<3>(((\"x\"<1>, ENumber<0>(9))), EId<2>(\"x\"))";
   ttag "tag4" "let x=9,y=55 in x" "ELet<5>(((\"x\"<1>, ENumber<0>(9)), ( \"y\"<3>, ENumber<2>(55))), EId<4>(\"x\"))";
   ttag "tag5" "let x=9,y=55 in y" "ELet<5>(((\"x\"<1>, ENumber<0>(9)), ( \"y\"<3>, ENumber<2>(55))), EId<4>(\"y\"))";
        (* shadowing *)
   ttag "tag6" "let x=9,y=55 in (let x=2 in x)" "ELet<8>(((\"x\"<1>, ENumber<0>(9)), ( \"y\"<3>, ENumber<2>(55))), ELet<7>(((\"x\"<5>, ENumber<4>(2))), EId<6>(\"x\")))";

   ttag "tag7"
        "let z=(let x=(3 - 9) in x) in z"
        "ELet<8>(((\"z\"<6>, ELet<5>(((\"x\"<3>, EPrim2<2>(Minus, ENumber<0>(3), ENumber<1>(9)))), EId<4>(\"x\")))), EId<7>(\"z\"))";
 ]
;;

let rename_suite =
"rename_suite">:::
 [
   trename "rename1" "8" "ENumber<0>(8)";
   trename "rename2" "add1(8)" "EPrim1<1>(Add1, ENumber<0>(8))";
   trename "rename3" "let x=9 in x" "ELet<3>(((\"x#1\"<1>, ENumber<0>(9))), EId<2>(\"x#1\"))";
   trename "rename4" "let x=9,y=55 in x" "ELet<5>(((\"x#1\"<1>, ENumber<0>(9)), (\"y#3\"<3>, ENumber<2>(55))), EId<4>(\"x#1\"))";
   trename "rename5" "let x=9,y=55 in y" "ELet<5>(((\"x#1\"<1>, ENumber<0>(9)), (\"y#3\"<3>, ENumber<2>(55))), EId<4>(\"y#3\"))";
   trename "rename6" "let x=9,y=55,z=88 in y" "ELet<7>(((\"x#1\"<1>, ENumber<0>(9)), (\"y#3\"<3>, ENumber<2>(55)), (\"z#5\"<5>, ENumber<4>(88))), EId<6>(\"y#3\"))";
   trename "rename7" "let x=9,y=55,z=88 in z" "ELet<7>(((\"x#1\"<1>, ENumber<0>(9)), (\"y#3\"<3>, ENumber<2>(55)), (\"z#5\"<5>, ENumber<4>(88))), EId<6>(\"z#5\"))";
 ]

let anf_suite =
"anf_suite">:::
 [

  tanf_4410 "forty_one_anf"
       (ENumber(41L, ()))
       forty_one_a;

  tanf_4410 "prim2"
       (EPrim2(Times, ENumber(41L, ()), ENumber(3L, ()), ()))
       (ELet([("$prim2_2", EPrim2(Times, ENumber(41L, ()), ENumber(3L, ()), ()), ())], EId("$prim2_2", ()), ()));

  (* For CS4410 students, with unnecessary let-bindings *)
  tanf_4410 "sub1(55)  *prim1_anf_4410*"
       (EPrim1(Sub1, ENumber(55L, ()), ()))
       (ELet(["$prim1_1", EPrim1(Sub1, ENumber(55L, ()), ()), ()],
             EId("$prim1_1", ()),
             ()));

  tanf_4410 "2 * sub1(55)"
       (EPrim2(Times, ENumber(2L,()), (EPrim1(Sub1, ENumber(55L, ()), ())), ()))
       (ELet([("$prim1_2", EPrim1(Sub1, ENumber(55L, ()), ()), ())],
         ELet([("$prim2_3", EPrim2(Times, ENumber(2L, ()), EId("$prim1_2", ()), ()), ())],
              EId("$prim2_3", ()),
              ()),
         ()));

  tanf_4410 "sub1(3 - 9)"
       (EPrim1(Sub1, EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ()))
       (ELet([("$prim2_2", EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())],
             ELet([("$prim1_3", EPrim1(Sub1, EId("$prim2_2",()), ()), ())],
                  EId("$prim1_3", ()),
                  ()),
             ()));

  (* For CS6410 students, with optimized let-bindings *)
  tanf "sub1(55)  *prim1_anf_6410*"
       (EPrim1(Sub1, ENumber(55L, ()), ()))
       (EPrim1(Sub1, ENumber(55L, ()), ()));

  tanf "2 * sub1(55)"
       (EPrim2(Times, ENumber(2L,()), (EPrim1(Sub1, ENumber(55L, ()), ())), ()))
       (ELet([("$prim1_2", EPrim1(Sub1, ENumber(55L, ()), ()), ())],
         EPrim2(Times, ENumber(2L,()), EId("$prim1_2",()), ()),
         ()));

  tanf "sub1(3 - 9)"
       (EPrim1(Sub1, EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ()))
       (ELet([("$prim2_2", EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())],
             EPrim1(Sub1, EId("$prim2_2",()), ()),
             ()));

  tanf "if 3: 1 else: 0"
       (EIf(ENumber(3L,()), ENumber(1L,()), ENumber(0L,()), ()))
       (EIf(ENumber(3L,()), ENumber(1L,()), ENumber(0L,()), ()));

  tanf "if (add1 4): 1 else: 0"
       (EIf(EPrim1(Add1, ENumber(4L,()), ()), ENumber(1L,()), ENumber(0L,()), ()))
       (ELet([("$prim1_1", EPrim1(Add1, ENumber(4L,()), ()), ())],
             (EIf(EId("$prim1_1",()), ENumber(1L,()), ENumber(0L,()), ())),
             ()));

  tanf "let x=0 in 2"
       (ELet([("x",ENumber(0L,()),())], ENumber(2L,()), ()))
       (ELet([("x",ENumber(0L,()),())], ENumber(2L,()), ()));

  tanf "let x=0 in x"
       (ELet([("x",ENumber(0L,()),())], EId("x",()), ()))
       (ELet([("x",ENumber(0L,()),())], EId("x",()), ()));

  (* todo should ANF break apart multi let-bindings
   * note to us--yes, we should have nested lets (instead of a single let with
   * multiple bindings)
  tanf "let x=0,y=1 in x"
       (ELet([("x",ENumber(0L,()),()); ("y",ENumber(1L,()),())], EId("x",()), ()))
       (ELet([("x",ENumber(0L,()),()); ("y",ENumber(1L,()),())], EId("x",()), ()));

  tanf "let x=0,y=1 in y"
       (ELet([("x",ENumber(0L,()),()); ("y",ENumber(1L,()),())], EId("y",()), ()))
       (ELet([("x",ENumber(0L,()),()); ("y",ENumber(1L,()),())], EId("y",()), ()));*)

  tanf "(let x=3-9 in x) + (let y=9-3 in y)"
       (EPrim2(Minus, (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())], EId("x",()), ())),
                      (ELet([("y",EPrim2(Minus, ENumber(9L,()), ENumber(3L,()), ()), ())], EId("y",()), ())), ()))
       (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()),())],
            (ELet([("y",EPrim2(Minus, ENumber(9L,()), ENumber(3L,()), ()),())],
                (EPrim2(Minus, EId("x",()), EId("y",()), ()))
                ,()))
            ,()));

  tanf "let x=3-9 in x"
       (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())], EId("x",()), ()))
       (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())], EId("x",()), ()));

  tanf "let z=1 in (let x=3-9 in x)"
       (ELet([("z", ENumber(1L, ()), ())],
             (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())],
                   EId("x",()),
                   ())),
             ()))
       (ELet([("z", ENumber(1L, ()), ())],
             (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())],
                   EId("x",()),
                   ())),
             ()));

  tanf "let z=1 in (let x=3-9 in z)"
       (ELet([("z", ENumber(1L, ()), ())],
             (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())],
                   EId("z",()),
                   ())),
             ()))
       (ELet([("z", ENumber(1L, ()), ())],
             (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())],
                   EId("z",()),
                   ())),
             ()));

  tanf "let z=1,x=2 in z"
       (ELet([("z", ENumber(1L, ()), ()); ("x", ENumber(2L, ()), ())], EId("z",()), ()))
       (ELet([("z", ENumber(1L, ()), ())],
             (ELet([("x", ENumber(2L, ()), ())],
                   EId("z", ()),
                   ())),
            ()));

  tanf "let z=1,x=2 in x"
       (ELet([("z", ENumber(1L, ()), ()); ("x", ENumber(2L, ()), ())], EId("x",()), ()))
       (ELet([("z", ENumber(1L, ()), ())],
             (ELet([("x", ENumber(2L, ()), ())],
                   EId("x", ()),
                   ())),
            ()));

  tanf "let z=1,x=z in x"
       (ELet([("z", ENumber(1L, ()), ()); ("x", EId("z", ()), ())], EId("x",()), ()))
       (ELet([("z", ENumber(1L, ()), ())],
             (ELet([("x", EId("z", ()), ())],
                   EId("x", ()),
                   ())),
            ()));

  tanf "let z=(let x=3-9 in x) in z"
       (ELet([("z", (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())],
                          EId("x",()),
                          ())),
              ())],
             EId("z",()),
             ()))
       (ELet([("x", EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())],
             (ELet([("z", EId("x", ()), ())], EId("z",()), ())),
             ()));

  tanf "let z=(add1 (3 - 9)) in z"
       (ELet([("z", EPrim1(Add1, EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ()), ())], EId("z", ()), ()))
       (ELet([("$prim2_2", EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()),())],
             ELet([("z", EPrim1(Add1, EId("$prim2_2", ()), ()), ())],
                  EId("z", ()),
                  ()),
             ()));

  (* TODO tanf where we operate on the vars in the body of a let expr *)
 ]


let suite =
"suite">:::
 [
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
  run_test_tt_main rename_suite;
  run_test_tt_main anf_suite;
  run_test_tt_main suite
;;
