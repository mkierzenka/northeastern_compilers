open Test_funcs

let tests_from_eggeater = [
  (* Tuples (nested) and outputs *)
  t "0tup" "()" "" "()";
  t "1tup_1" "(6,)" "" "(6,)";
  t "1tup_2" "(false,)" "" "(false,)";
  t "pair_1" "(1,2)" "" "(1, 2)";
  t "pair_2" "(1,(true,8))" "" "(1, (true, 8))";
  t "trip_1" "(true,false,7)" "" "(true, false, 7)";
  t "trip_2" "(true,(),7)" "" "(true, (), 7)";
  t "trip_3" "((16,),(),7)" "" "((16,), (), 7)";
  t "trip_4" "((16,),(),(true,18,20))" "" "((16,), (), (true, 18, 20))";

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
  terr "get_idx_bool" "(0,1)[false]" "" "tuple-get index not numeric";
  terr "get_neg_idx" "(1,2)[-1]" "" "index too small";
  terr "get_big_idx0" "()[0]" "" "index too large to get";
  terr "get_big_idx1" "(1,)[1]" "" "index too large to get";
  terr "get_big_idx2" "(1,2)[2]" "" "index too large to get";

  (* SetItem *)
  t "set_item_0" "(1,)[0] := 6" "" "(6,)";
  t "set_item_1" "(1,2)[1] := 6" "" "(1, 6)";
  t "set_item_2" "(1,2)[1] := false" "" "(1, false)";
  t "set_item_3" "(1,2,true,false)[0] := false" "" "(false, 2, true, false)";
  t "set_item_4" "(1,2,(8,7),false)[2] := (20,5,6)" "" "(1, 2, (20, 5, 6), false)";
  t "set_item_5" "((true,9),2,(8,7),false)[2] := (20,5,6)" "" "((true, 9), 2, (20, 5, 6), false)";
  terr "set_from_num" "7[0]:=true" "" "expected tuple";
  terr "set_from_bool" "false[0]:=false" "" "expected tuple";
  terr "set_idx_bool" "(0,1)[false] := true" "" "tuple-set index not numeric";
  terr "set_idx_nil" "(0,1)[nil] := true" "" "tuple-set index not numeric";
  terr "set_neg_idx" "(1,2)[-1]:=3" "" "index too small";
  terr "set_big_idx0" "()[0]:=2" "" "index too large to get";
  terr "set_big_idx1" "(1,)[1]:=2" "" "index too large to get";
  terr "set_big_idx2" "(1,2)[2]:=9" "" "index too large to get";

  (* Tuples and lets *)
  t "tup_let_3" "let t=(print(1),print((2,3))) in print(t)" "" "1\n(2, 3)\n(1, (2, 3))\n(1, (2, 3))";
  (* ran out of time, didn't get these cases to work (for both lets and functions) :( *)
  (*terr "tup_let_mismatch3" "let temp = (1,2,3) in let (a,b) = temp in 7" "" "index too big";
  terr "tup_let_mismatch4" "let temp=(1,2,3) in let (a,b) = temp in true" "" "index too big";
  terr "tup_let_mismatch5" "let temp=(1,2,3), (a,b) = temp in true" "" "index too big";*)
  (* see partial_tuple_breakdowns.egg *)

  (* Lets and blanks *)
  (* see partial_tuple_breakdowns.egg *)

  (* input tests *)
  t "input_1" "input()" "16" "16";
  t "input_2" "print(input())" "16" "16\n16";
  t "input_3" "let inp=input() in 10 + 100 * inp" "-2" "-220";
  t "input_4a" "let inp=input() in if isnum(inp): 2 * inp else: !(inp)" "33" "66";
  t "input_4b" "let inp=input() in if isnum(inp): 2 * inp else: !(inp)" "false" "true";
  t "input_5" "if isnum(input()): 2 else: false" "10" "2";
  terr "input_err1" "if isnum(input()): 2 else: false" "(2,)" "bad input, input must be a number or a bool";
  terr "input_err2" "if isnum(input()): 2 else: false" "()" "bad input, input must be a number or a bool";
  terr "input_err3" "if isnum(input()): 2 else: false" "nil" "bad input, input must be a number or a bool";
  terr "input_err4" "if isnum(input()): 2 else: false" "(-1, 4)" "bad input, input must be a number or a bool";
  terr "input_err5" "if isnum(input()): 2 else: false" "bogus_input" "bad input, input must be a number or a bool";
  t "input_bool1" "print(input())" "true" "true\ntrue";
  t "input_bool2" "print(input())" "false" "false\nfalse";
  t "input_bool3" "let inp=input() in (if isnum(inp): -99 else: (if isbool(inp): inp else: -99))" "true" "true";
  t "input_multi1" "let x=input() in x" "-444 555" "-444";
  t "input_multi2" "let x=input() in x" "-444 false" "-444";
  t "input_multi3" "let x=input() in x" "false 8" "false";

  (* nil tests *)
  t "print_nil" "let x=nil in print(x)" "" "nil\nnil";
  t "print_tup_of_nil" "let x=nil in print((x,))" "" "(nil,)\n(nil,)";
  t "print_nil_tups" "let x=nil in print((((x,),),))" "" "(((nil,),),)\n(((nil,),),)";
  t "print_tup_of_nil2"
    "let x=4, y=1, z=45, w=nil in print((x,y,((x,nil),),(),(w,),(w),(x,x * z),(z,)))"
    ""
    "(4, 1, ((4, nil),), (), (nil,), nil, (4, 180), (45,))\n(4, 1, ((4, nil),), (), (nil,), nil, (4, 180), (45,))";
  t "nil_not_unit" "nil == ()" "" "false";
  t "nil_is_nil" "nil == nil" "" "true";
  t "nil_is_tup" "istuple(nil)" "" "true";
  terr "get_nil" "nil[0]" "" "tried to access component of nil";
  terr "set_nil_1" "nil[0]:=true" "" "tried to access component of nil";
  terr "set_nil_2" "let x=nil in (x[0]:=true)" "" "tried to access component of nil";

  (* simple func decls with _ *)
  t "decls_with_underscore_1" "def f(a,_,b): b - a  f(10,101,6)" "" "-4";
  t "decls_with_underscore_2" "def f(_): 17  f(111)" "" "17";
  t "decls_with_underscore_3" "def f(_): input()  f(111)" "88" "88";

  (* make sure cprint doesn't cause any issues *)
  t "decl_cprint_1" "def cprint(): 88  1 + print(101)" "" "101\n102";
  t "decl_cprint_2" "def cprint(): 88  1 + cprint()" "" "89";
  terr "decl_cprint_3" "def cprint(): 88  cprint(200)" "" "expected an arity of 0, but received 1 arguments";

  (* sequence tests *)
  t "seq_1" "17; 57" "" "57";
  t "seq_2" "print(17); 57" "" "17\n57";
  t "seq_3" "let a=print(17) in print(a); a+1" "" "17\n17\n18";
  terr "seq_4_l" "(let a=print(17) in print(a)); a+1" "" "The identifier a, used at ";
  terr "seq_4_r" "(let a=print(17) in print(a)); a+1" "" ", is not in scope";
  t "seq_6" "true || (print(false) ; 200)" "" "true";
  t "seq_7" "false || (100; true)" "" "true";

  (* extra tuple tests *)
  t "extra_tup_1" "let t=(8, (true, false), 99) in t[1][0] := 7; t" "" "(8, (7, false), 99)";
  t "extra_tup_2" "let t=(8, (true, false), 99) in t[1][1] := true; t" "" "(8, (true, true), 99)";
  t "extra_tup_3" "let t=(8, (true, false), 99) in t[1][1] := (1,2,3); t" "" "(8, (true, (1, 2, 3)), 99)";
  t "extra_tup_4" "let t=(8, (true, false), 99) in t[1][1] := (1,(2,),3)[1]; t" "" "(8, (true, (2,)), 99)";
  t "extra_tup_5" "let t=(8, (true, false), 99) in t[0] := sub1(t[0]); t" "" "(7, (true, false), 99)";

  (* istuple tests *)
  t "is_tuple_1" "istuple(8)" "" "false";
  t "is_tuple_2" "istuple(())" "" "true";
  t "is_tuple_3" "istuple((true,))" "" "true";
  t "is_tuple_4" "istuple((true,88))" "" "true";
  t "is_tuple_5" "istuple((true,88)[0])" "" "false";
  t "is_tuple_6" "istuple(((),88)[0])" "" "true";
  t "is_tuple_7" "istuple((nil,88)[0])" "" "true";
  t "is_tuple_8" "istuple(nil)" "" "true";

  (* inputs tests *)
  t "no_captured_input" "let x=6,y=7 in x*y" "100\n88" "42";
  t "some_captured_input" "let x=6,y=7 in x*input()" "100\n88" "600";
  t "two_inputs" "let x=input(),y=input() in x*y" "6\n7" "42";
  t "three_inputs" "let x=input(),y=input() in x*y + input()" "3\n4\n10" "22";

  (* equal tests *)
  t "equal_ints" "let x = 5 in equal(sub1(x) + 1, print(x))" "" "5\ntrue";
  t "equal_neg_ints" "let x = -999 in equal(sub1(x) + 1, print(x))" "" "-999\ntrue";
  t "equal_bools" "let x = false, y = !(x) in equal(true && !(y), x)" "" "true";
  t "unequal_ints" "let x = 5 in equal(add1(x), x)" "" "false";
  t "unequal_bools" "let x = true in equal(x, false)" "" "false";
  t "unequal_bool_int" "let x = true, y = if x: 7 else: true in equal(x, y)" "" "false";
  t "unequal_int_bool" "let x = true, y = if x: 7 else: true in equal(y, x)" "" "false";
  t "equal_nil" "equal(nil, nil)" "" "true";
  t "equal_tups_empty" "equal((), ())" "" "true";
  t "equal_tups_literal" "let tup=(1,false) in equal(tup, tup)" "" "true";
  t "equal_tups_literal2" "let tup=(1,false), tup2 = tup in equal(tup, tup2)" "" "true";
  t "equal_tups_struct" "let tup=(1,false) in equal((1,false), tup)" "" "true";
  t "equal_tups"
    "let tup=(true, (), (nil,), 8, (false, false, 4)),
         tup2=(true, (), (nil,), add1(tup[3]), (false, false, 4))
     in equal(tup, tup2[3]:=8)"
    "" "true";
  t "equal_tups2" "let tup=(true, (), (nil,), (false, false, 4)) in equal(tup, tup[1]:=(1,2))" "" "true";
  t "unequal_tups" "equal((), (1,))" "" "false";
  t "unequal_tups0a" "equal((), nil)" "" "false";
  t "unequal_tups0b" "equal(nil, ())" "" "false";
  t "unequal_tups0c" "equal((nil,), nil)" "" "false";
  t "unequal_tups1" "equal((1,), ())" "" "false";
  t "unequal_tups2" "equal((1,2), (1,))" "" "false";
  t "unequal_tups3" "equal((true,false, 1, nil), (true, false, 2, nil))" "" "false";
  t "unequal_tups_literal" "let tup=(1,false) in equal(tup, tup[0]:=2)" "" "true";
  t "unequal_tups_literal2" "let tup=(1,false) in equal(tup[0]:=2, tup)" "" "true";
]

(* These fail at the moment because of a desugaring ASeq issue, we think *)
let eggeater_aseq_issues = [
    t "tup_let_0" "let (z) = (false,) in z" "" "false";
  t "tup_let_1" "let (a,b) = (5,4) in a - b" "" "1";
  t "tup_let_1b" "let tup = (5,4) in let (a,b) = tup in a - b" "" "1";
  t "tup_let_1c" "let tup = (5,4), (a,b) = tup in a - b" "" "1";
  t "tup_let_2" "let ((a,b),_,(x,y,z)) = ((5,4),print(-99),(1,2,3)) in (a*b) - (x*y*z)" "" "-99\n14";
  t "tup_let_4"
    "let (i0, i1, _, i3) = ((let i0=false in !(i0)), (9,), 4, 3) in (if i0: i1[0] * 4 - 3 else: -99)"
    "" "33";
  terr "tup_let_mismatch" "let (a,b) = (input(),) in true" "5" "index too big";
  terr "tup_let_mismatch2" "let (a,b,(c,d,e),f) = (1,2,(3,3),4) in 7" "" "index too big";
  t "lets_and_blanks" "let _=2 in 3" "" "3";
  t "lets_and_blanks2" "let _=print(1) in 2" "" "1\n2";
  t "lets_and_multiple_blanks"
    "let _=print(1), _=print(false), _=((print((-3,)),), print(4)) in true"
    "" "1\nfalse\n(-3,)\n4\ntrue";
  t "lets_and_multiple_blanks2"
    "let _=print(1) in
    let _=print(false), _=((print((-3,)),), print(4)) in true"
    "" "1\nfalse\n(-3,)\n4\ntrue";


  (* func with _ in args and _ in body *)
  t "decl_underscore_args_and_body" "def f(x,y,_): let z=y,_=z in add1(x)  f(1,2,3)" "" "3";


  (* decl with tuple args *)
  t "decl_tup_args_1" "def f((a,b), c): a+b+c  f((1,2),3)" "" "6";
  t "decl_tup_args_2" "def f(z,(a,b), c): z*(a+b+c)  f(100,(1,2),3)" "" "600";
  t "decl_tup_args_3" "def f(z,(a,_), c): z*(a+a+c)  f(100,(1,2),3)" "" "500";
  terr "decl_tup_args_4" "def f(z,(a,_), c): z*(a+a+c)  f(100,9,3)" "" "expected tuple";
]

(* These fail at the moment probablay because of a different desugaring issue *)
let eggeater_scif_issues = [
  t "seq_5" "true || print(false) ; print(6) ; 7" "" "6\n7";
]
