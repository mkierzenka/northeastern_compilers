open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs


let tag_of_string = string_of_int;;

let ast_of_tag_expr (e : tag expr) : string =
  format_expr e tag_of_string
;;

let tcheck_scope_run ?args:(args=[]) ?std_input:(std_input="") program name test_ctxt =
  let prog = parse_string name program in
  check_scope prog;
  assert true

let tcheck_scope (name : string) (program : string) : OUnit2.test =
  name>::tcheck_scope_run program name;;
;;

let ttag_run ?args:(args=[]) ?std_input:(std_input="") program name expected test_ctxt =
  let prog = parse_string name program in
  check_scope prog;
  assert_equal (Ok(expected)) (Ok(ast_of_tag_expr (tag prog))) ~printer:result_printer

let ttag (name : string) (program : string) (expected : string) : OUnit2.test =
  name>::ttag_run program name expected;;
;;

(* Runs a function true if throws correct exception *)
let tbind_except (name : string) (func : (unit -> unit)) (expected_msg : string) = name>::fun _ ->
  try (func() ; assert false) with
    | BindingError s -> assert_equal s expected_msg
	| _ -> assert false
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

let suite1 =
"check_scope_suite">:::
 [

  (*tbind_except "test1" (fun () -> (ignore (check_scope (parse_string "scratch" "(add1 1)")))) "saDSA"*)

   tcheck_scope "check_scope1" "8";
   tcheck_scope "check_scope2" "let x=9 in x";
   tcheck_scope "check_scope3" "let x=9 in add1(x)";
   tcheck_scope "check_scope4" "let x=9,y=77 in add1(x)";
   tcheck_scope "check_scope5" "let y=9,x=77 in add1(x)";

   te "check_scope_err1" "x" "unbound symbol x";
   te "check_scope_err2" "let x=9 in y" "unbound symbol y";
   te "check_scope_err3" "let x=9 in add1(y)" "unbound symbol y";
   te "check_scope_err4" "let x=9,z=33 in add1(y)" "unbound symbol y";

   ttag "tag1" "8" "ENumber<0>(8)";
   ttag "tag2" "add1(8)" "EPrim1<1>(Add1, ENumber<0>(8))";
   ttag "tag3" "let x=9 in x" "ELet<2>((( \"x\"<1>, ENumber<0>(9))), EId<1>(\"x\"))";
   ttag "tag4" "let x=9,y=55 in x" "ELet<3>((( \"x\"<2>, ENumber<1>(9)), ( \"y\"<1>, ENumber<0>(55))), EId<2>(\"x\"))";
   ttag "tag5" "let x=9,y=55 in y" "ELet<3>((( \"x\"<2>, ENumber<1>(9)), ( \"y\"<1>, ENumber<0>(55))), EId<2>(\"y\"))";

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
  run_test_tt_main suite1
  (* run_test_tt_main suite *)
;;
