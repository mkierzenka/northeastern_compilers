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
   ttag "tag2" "(8)" "ENumber<0>(8)";
   ttag "tag3" "add1(8)" "EPrim1<1>(Add1, ENumber<0>(8))";
   ttag "tag4" "sub1(8)" "EPrim1<1>(Sub1, ENumber<0>(8))";
   ttag "tag5" "4 + 5" "EPrim2<2>(Plus, ENumber<0>(4), ENumber<1>(5))";
   ttag "tag6" "4 - 5" "EPrim2<2>(Minus, ENumber<0>(4), ENumber<1>(5))";
   ttag "tag7" "4 * 5" "EPrim2<2>(Times, ENumber<0>(4), ENumber<1>(5))";
   ttag "tag8" "4 + (5 * 7)" "EPrim2<4>(Plus, ENumber<0>(4), EPrim2<3>(Times, ENumber<1>(5), ENumber<2>(7)))";

   (* if *)
   ttag "tag_if1" "if 6: 7 else: 8" "EIf<3>(ENumber<0>(6), ENumber<1>(7), ENumber<2>(8))";
   ttag "tag_if2" "if 6: 4 + 5 else: 8 + 9" "EIf<7>(ENumber<0>(6), EPrim2<3>(Plus, ENumber<1>(4), ENumber<2>(5)), EPrim2<6>(Plus, ENumber<4>(8), ENumber<5>(9)))";

   (* let *)
   ttag "tag_let1" "let x=9 in x" "ELet<3>(((\"x\"<1>, ENumber<0>(9))), EId<2>(\"x\"))";
   ttag "tag_let2" "let x=9,y=55 in x" "ELet<5>(((\"x\"<1>, ENumber<0>(9)), ( \"y\"<3>, ENumber<2>(55))), EId<4>(\"x\"))";
   ttag "tag_let3" "let x=9,y=55 in y" "ELet<5>(((\"x\"<1>, ENumber<0>(9)), ( \"y\"<3>, ENumber<2>(55))), EId<4>(\"y\"))";
   ttag "tag_let4"
        "let z=(let x=(3 - 9) in x) in z"
        "ELet<8>(((\"z\"<6>, ELet<5>(((\"x\"<3>, EPrim2<2>(Minus, ENumber<0>(3), ENumber<1>(9)))), EId<4>(\"x\")))), EId<7>(\"z\"))";
        (* shadowing *)
   ttag "tag_let5" "let x=9,y=55 in (let x=2 in x)" "ELet<8>(((\"x\"<1>, ENumber<0>(9)), ( \"y\"<3>, ENumber<2>(55))), ELet<7>(((\"x\"<5>, ENumber<4>(2))), EId<6>(\"x\")))";
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
  tanf "forty_one_anf"
       (ENumber(41L, ()))
       forty_one_a;

  tanf "prim1*"
       (EPrim1(Sub1, ENumber(55L, ()), ()))
       (EPrim1(Sub1, ENumber(55L, ()), ()));

  tanf "prim2"
       (EPrim2(Times, ENumber(41L, ()), ENumber(3L, ()), ()))
       (EPrim2(Times, ENumber(41L, ()), ENumber(3L, ()), ()));

  (* 2 * sub1(55) *)
  tanf "prim1_in_prim2"
       (EPrim2(Times, ENumber(2L,()), (EPrim1(Sub1, ENumber(55L, ()), ())), ()))
       (ELet([("$prim1_2", EPrim1(Sub1, ENumber(55L, ()), ()), ())],
         EPrim2(Times, ENumber(2L,()), EId("$prim1_2",()), ()),
         ()));

  (* sub1(3 - 9) *)
  tanf "prim2_in_prim1"
       (EPrim1(Sub1, EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ()))
       (ELet([("$prim2_2", EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())],
             EPrim1(Sub1, EId("$prim2_2",()), ()),
             ()));

  (* (let x=3-9 in x) + (let y=9-3 in y) *)
  tanf "prim2_with_lets"
       (EPrim2(Minus, (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())], EId("x",()), ())),
                      (ELet([("y",EPrim2(Minus, ENumber(9L,()), ENumber(3L,()), ()), ())], EId("y",()), ())), ()))
       (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()),())],
            (ELet([("y",EPrim2(Minus, ENumber(9L,()), ENumber(3L,()), ()),())],
                (EPrim2(Minus, EId("x",()), EId("y",()), ()))
                ,()))
            ,()));

  (* if 3: 1 else: 0 *)
  tanf "if_simple"
       (EIf(ENumber(3L,()), ENumber(1L,()), ENumber(0L,()), ()))
       (EIf(ENumber(3L,()), ENumber(1L,()), ENumber(0L,()), ()));

  (* if (add1 4): 1 else: 0 *)
  tanf "if_cond"
       (EIf(EPrim1(Add1, ENumber(4L,()), ()), ENumber(1L,()), ENumber(0L,()), ()))
       (ELet([("$prim1_1", EPrim1(Add1, ENumber(4L,()), ()), ())],
             (EIf(EId("$prim1_1",()), ENumber(1L,()), ENumber(0L,()), ())),
             ()));

  (* if (add1 4): (3 - 9) else: (sub1 88) *)
  tanf "if_with_sub_exprs"
       (EIf(EPrim1(Add1, ENumber(4L,()), ()),
            EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()),
            EPrim1(Sub1, ENumber(88L,()), ()),
        ()))
       (ELet([("$prim1_1", EPrim1(Add1, ENumber(4L,()), ()), ())],
            EIf(EId("$prim1_1", ()),
                EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()),
                EPrim1(Sub1, ENumber(88L,()), ()),
                ()),
        ()));

  (* if (if 0: add1(4) else: 4): 1 else: 0 *)
  tanf "if_nested_if_cond"
       (EIf(EIf(ENumber(0L,()),
                 EPrim1(Add1, ENumber(4L,()), ()),
                 ENumber(4L,()),
                 ()),
            ENumber(1L,()),
            ENumber(0L,()),
            ()))
        (ELet([("$if_4",
                EIf(ENumber(0L,()),
                    EPrim1(Add1, ENumber(4L,()), ()),
                    ENumber(4L,()),
                    ()), ())],
              EIf(EId("$if_4", ()), ENumber(1L,()), ENumber(0L,()), ()),
              ()));

  (* if (if (3 - 9): sub1(2) else: sub1(3)): 1 else: 0 *)
  tanf "if_nested_if_cond2"
       (EIf(EIf(EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()),
                 EPrim1(Sub1, ENumber(2L,()), ()),
                 EPrim1(Sub1, ENumber(3L,()), ()),
                 ()),
            ENumber(1L,()),
            ENumber(0L,()),
            ()))
       (ELet([("$prim2_2", EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())],
             ELet([("$if_7",
                   EIf(EId("$prim2_2", ()),
                       EPrim1(Sub1, ENumber(2L,()), ()),
                       EPrim1(Sub1, ENumber(3L,()), ()),
                       ()),
                   ())],
                   EIf(EId("$if_7", ()), ENumber(1L,()), ENumber(0L,()), ()),
                   ()),
             ()));

  (* let x=0 in 2 *)
  tanf "let_simple_unused"
       (ELet([("x",ENumber(0L,()),())], ENumber(2L,()), ()))
       (ELet([("x",ENumber(0L,()),())], ENumber(2L,()), ()));

  (* let x=0 in x *)
  tanf "let_simple"
       (ELet([("x",ENumber(0L,()),())], EId("x",()), ()))
       (ELet([("x",ENumber(0L,()),())], EId("x",()), ()));

  (* let x=3-9 in x *)
  tanf "let_prim2_binding"
       (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())], EId("x",()), ()))
       (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())], EId("x",()), ()));

  (* let z=1 in (let x=3-9 in x) *)
  tanf "let_nested_let_body"
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

  (* let z=1 in (let x=3-9 in z) *)
  tanf "let_nested_let_body2"
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

  (* let z=(add1 (3 - 9)) in z *)
  tanf "let_nested_let_bindings"
       (ELet([("z", EPrim1(Add1, EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ()), ())], EId("z", ()), ()))
       (ELet([("$prim2_2", EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()),())],
             ELet([("z", EPrim1(Add1, EId("$prim2_2", ()), ()), ())],
                  EId("z", ()),
                  ()),
             ()));

  (* let z=(let x=3-9 in x) in z *)
  tanf "let_nested_let_bindings2"
       (ELet([("z", (ELet([("x",EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())],
                          EId("x",()),
                          ())),
              ())],
             EId("z",()),
             ()))
       (ELet([("x", EPrim2(Minus, ENumber(3L,()), ENumber(9L,()), ()), ())],
             (ELet([("z", EId("x", ()), ())], EId("z",()), ())),
             ()));

  (* let x=1,y=2,z=4 in x *)
  tanf "let_multi_bindings"
       (ELet([("x", ENumber(1L, ()), ()); ("y", ENumber(2L, ()), ()); ("z", ENumber(4L, ()), ())], EId("x",()), ()))
       (ELet([("x", ENumber(1L, ()), ())],
             (ELet([("y", ENumber(2L, ()), ())],
                   ELet([("z", ENumber(4L, ()), ())],
                        EId("x", ()),
                        ()),
                   ())),
            ()));

  (* let x=1,y=2,z=4 in y *)
  tanf "let_multi_bindings1"
       (ELet([("x", ENumber(1L, ()), ()); ("y", ENumber(2L, ()), ()); ("z", ENumber(4L, ()), ())], EId("y",()), ()))
       (ELet([("x", ENumber(1L, ()), ())],
             (ELet([("y", ENumber(2L, ()), ())],
                   ELet([("z", ENumber(4L, ()), ())],
                        EId("y", ()),
                        ()),
                   ())),
            ()));

  (* let x=1,y=2,z=4 in z *)
  tanf "let_multi_bindings2"
       (ELet([("x", ENumber(1L, ()), ()); ("y", ENumber(2L, ()), ()); ("z", ENumber(4L, ()), ())], EId("z",()), ()))
       (ELet([("x", ENumber(1L, ()), ())],
             (ELet([("y", ENumber(2L, ()), ())],
                   ELet([("z", ENumber(4L, ()), ())],
                        EId("z", ()),
                        ()),
                   ())),
            ()));

  (* let z=1,x=z in x *)
  tanf "let_dependent_bindings"
       (ELet([("z", ENumber(1L, ()), ()); ("x", EId("z", ()), ())], EId("x",()), ()))
       (ELet([("z", ENumber(1L, ()), ())],
             (ELet([("x", EId("z", ()), ())],
                   EId("x", ()),
                   ())),
            ()));

  (* let z=1,x=z in let z=6 in z *)
  tanf "shadowing_mul_lets"
       (ELet([("z", ENumber(1L, ()), ()); ("x", EId("z", ()), ())],
             ELet(["z", ENumber(6L,()), ()], EId("z",()), ()),
             ()))
       (ELet([("z", ENumber(1L, ()), ())],
             ELet([("x", EId("z", ()), ())],
                 ELet([("z", ENumber(6L, ()), ())],
                     EId("z", ()),
                     ()),
                 ()),
             ()));
 ]


let suite =
"suite">:::
 [
  ta "forty_one_run_anf" (tag forty_one_a) "41";
  t "forty_one" forty_one "41";
  t "neg_forty_one" "-41" "-41";

  (* Add1 / Sub1 *)
  t "add1" "add1(4)" "5";
  t "sub1" "sub1(4)" "3";
  t "sub_add" "add1(sub1(44))" "44";
  t "add_sub" "sub1(add1(40))" "40";
  t "add_add" "add1(add1(111))" "113";
  t "sub_sub" "sub1(sub1(1000))" "998";

  (* Add1 / Sub1 Errors *)
  te "add1_multi" "add1(2 4)" "Parse error";
  te "sub1_multi" "sub1(2 4)" "Parse error";

  (* Binary Operator *)
  t "binop_1" "4 - 3" "1";
  t "binop_7" "4 - -3" "7";
  t "binop_minus1" "4 - 3 - 2" "-1";
  t "binop_12" "8 + (2*2)" "12";
  t "binop_20" "(8 + 2)*2" "20";
  t "binop" "add1(2) + sub1(3)" "5";
  t "binop_lets" "(let x = 1 in x) + (let x = 2 in x)" "3";
    (* These "bad pemdas" cases are on purpose, as specified in Assignment 3 Section 1.3 *)
  t "binop_20_bad_pemdas" "8 + 2*2" "20";
  t "binop_bad_pemdas2" "2 * 3 + 1 * 7" "49";
  t "binop_bad_pemdas3" "2 * (3 + 1) * 7" "56";
  t "binop_bad_pemdas4" "2 * add1(3) * 7" "56";
  te "binop_minus_neg" "1-2" "Parse error at line 1, col 3: token `-2`";

  (* Let bindings correct *)
  t "let" "let x=10 in x" "10";
  t "let_const" "let a=7 in 71" "71";
  t "let_var" "let a=7 in add1(a)" "8";
  t "let_multi_bindings_m" "let m=11,n=22,o=33,p=44,q=55,r=66,s=77 in m" "11";
  t "let_multi_bindings_q" "let m=11,n=22,o=33,p=44,q=55,r=66,s=77 in q" "55";
  t "let_multi_bindings_s" "let m=11,n=22,o=33,p=44,q=55,r=66,s=77 in s" "77";
  t "let_complex_bind" "let a=4, b=add1(sub1(add1(2))) in b" "3";
  t "let_nested_bind_multi" "let g=-99,h=g,i=h,final=add1(i) in final" "-98";
  t "let_chain_body" "let a=1,b=2 in (let c=3 in (let d=4,e=5 in c))" "3";
  t "let_val_if" "let x=(if sub1(1): 0 else: 44) in x" "44";
  t "let_val_binop_0" "let x=(2 + (9*3))*0 in x" "0";
  t "let_val_binop_58" "let x=(2 + (9*3))*2 in x" "58";
  t "let_if_t" "let y=1 in if y: add1(6) else: 8+3" "7";
  t "let_if_f" "let y=0 in if y: add1(6) else: 8+3" "11";
  t "let_if_add" "let y=0 in if add1(y): sub1(6) else: 8+3" "5";
  t "let_if_add2" "let y=10 in let y=0 in if 1: sub1(y) else: 8+3" "-1";
  t "let_if_add3" "let y=10 in let y=0 in if 0: sub1(y) else: add1(y)" "1";
  tprog "shadowing.boa" "66";
  tprog "shadowing_mul_lets.boa" "6";
  tprog "test1.boa" "3";
  tprog "let_chain.boa" "2";
  tprog "let_chain2.boa" "1000";
  tprog "let_from_prof.boa" "48";

  (* Let bindings errors *)
  te "let_dup_binds" "let x=1,x=1 in 2" "Multiple bindings of x";
  te "let_dup_binds2" "let x=1,x=3 in 2" "Multiple bindings of x";
  te "let_dup_binds3" "let x=1,y=9,x=1 in 2" "Multiple bindings of x";
  te "let_dup_binds4" "let x=1,y=9,z=33,x=3 in 2" "Multiple bindings of x";
  te "binding_err0" "let in y" "Parse error at line 1, col 6: token `in`";
  teprog "binding_err1.boa" "Unbound symbol y at binding_err1.boa, 1:11-1:12";
  teprog "binding_err2.boa" "Unbound symbol z at binding_err2.boa, 1:6-1:7";
  te "binding_err1" "let x=8 in y" "Unbound symbol y at binding_err1, 1:11-1:12";
  te "binding_err2" "let x=z in let x=66 in x" "Unbound symbol z at binding_err2, 1:6-1:7";
  te "binding_err3" "let x=(let y=8 in p) in let x=66 in x" "Unbound symbol p at binding_err3, 1:18-1:19";
  te "binding_err4" "let x=(let y=r in p) in let x=66 in x" "Unbound symbol r at binding_err4, 1:13-1:14";
  te "binding_err5" "let x=(let y=  r in p) in let x=66 in x" "Unbound symbol r at binding_err5, 1:15-1:16";
  te "binding_err6" "let x=(if x: 0 else: 1) in x" "Unbound symbol x at binding_err6, 1:10-1:11";
  teprog "let_chain2_err.boa" "Unbound symbol innerinner";

  te "let_rebind_add1" "let add1=4 in 5" "Parse error at line 1, col 8: token `add1`";
  te "let_rebind_add1_used" "let add1=4 in add1" "Parse error at line 1, col 8: token `add1`";
  te "let_rebind_add1_used2" "let add1=4 in add1(add1)" "Parse error at line 1, col 8: token `add1`";
  te "let_rebind_sub1" "let  sub1=4 in 5" "Parse error at line 1, col 9: token `sub1`";
  te "let_rebind_let" "let let=4 in let" "Parse error at line 1, col 7: token `let`";

  (* If *)
  t "if1" "if 5: 4 else: 2" "4";
  t "if2" "if 0: 4 else: 2" "2";
  t "if3" "if sub1(1): 4 else: 2" "2";
  t "if4" "if 0: 2 else: add1(add1(1 + 2))" "5";
  t "if5" "if 1: 2 else: add1(add1(1 + 2))" "2";
  t "if6" "if (if 0: 0 else: 1): 2 else: 9" "2";
  t "if7" "if (if 1: 0 else: 1): 2 else: 9" "9";
  t "if8" "if (let x=1 in x): (let x = 2 in x) else: (let x = 3 in x)" "2";
  t "if9" "if (let x=0 in x): (let x = 2 in x) else: (let x = 3 in x)" "3";

  (* If errors *)
  te "if_err1" "if (let x=1 in x): x else: 9" "Unbound symbol x";
  te "if_err2" "if (let x=0 in x): x else: 9" "Unbound symbol x";
  te "if_err3" "if (let x=0 in x): 9 else: x" "Unbound symbol x";
  te "if_err4" "if 1: (let x=0 in x) else: x" "Unbound symbol x";
  te "if_err5" "if 1: x else: (let x=0 in x)" "Unbound symbol x";
  te "if_err6" "if 0: (let x=0 in x) else: x" "Unbound symbol x";
  te "if_err7" "if x: (let x=1 in x) else: (let x=0 in x)" "Unbound symbol x";
  ]
;;


let () =
  run_test_tt_main check_scope_suite;
  run_test_tt_main tag_suite;
  run_test_tt_main rename_suite;
  run_test_tt_main anf_suite;
  run_test_tt_main suite
;;
