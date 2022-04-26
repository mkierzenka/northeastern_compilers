
(* This file contains 2 different test groups. The first (tests_for_free_vars) is from FDL and was testing the free_vars function.
The 2nd (fvs_tests) is from Racer and was testing the free_vars_cache function. *)

(* TODO- do we need both the fv functions? Should coallesce these tests into 1 suite probably *)

(* 
let tfvs name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    match anfed with
    | AProgram(body, _) ->
      let vars = free_vars body in
      let c = Stdlib.compare in
      let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in
      assert_equal (List.sort c expected) (List.sort c vars) ~printer:str_list_print)
*)

(*
let tfvs name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let desug = desugar ast in
    let tagged = tag desug in
    let renamed = rename_and_tag tagged in
    let anfed = anf (tag renamed) in
    let fv_prog = free_vars_cache anfed in
    assert_equal expected (string_of_aprogram_with_fvs fv_prog) ~printer:(fun s -> s))
*)


let tests_for_free_vars = [
  t "new_func1" "def f(x): add1(x)  f(2)" "" "3";
  tfvs "new_func1_fvs" "let rec f = (lambda(x): add1(x)) in  f(2)" [];
  tfvs "in_lambda_fvs" "(lambda(x): add1(x))" [];

  t "new_func2let" "let f = (lambda(x): add1(x)) in f(2)" "" "3";
  t "new_func2letrec" "let rec f = (lambda(x): add1(x)) in f(2)" "" "3";
  t "new_func2trick" "let f = (lambda(x): let y=1 in add1(x)) in f(2)" "" "3";
  t "new_func3" "let f = (lambda(x,y): x+y) in f(2,3)" "" "5";

  tfvs "tfvs_imm" "true" [];
  tfvs "tfvs_prim2_1" "x + x" ["x"];
  tfvs "tfvs_prim2_2" "a * b" ["a";"b"];
  tfvs "tfvs_let" "let x=3,z=x+1 in x < (2 + y)" ["y"];
  tfvs "tfvs_nested_let" "let x=(let y=false in !(y) && z) in (let w = -99 in w*h)" ["z"; "h"];
  tfvs "tfvs_if_and_tup" "if false: (let tup=(4,false,a),ww=22 in tup[z]:=y;tup[0]:=z) else: ww" ["a"; "ww"; "z"; "y"];
  tfvs "tfvs_app" "add1(func(a,(a,c),3,b,true))" ["func"; "a"; "c"; "b"];
  tfvs "tfvs_app_lambda" "let x=10 in (let f = (lambda(y): x + y) in f(10))" [];
  tfvs "tfvs_app_lambda2" "let x=10,y=11,z=12 in (let f = (lambda(a): x + y + z) in f(10))" [];
  tfvs "tfvs_letrec" "let rec f1 = (lambda(x): x * f2(x)), f2=(lambda(x): x + y) in f1(7)" ["y"];
  tfvs "tfvs_letrec_flipped" "let rec f2=(lambda(x): x + y), f1 = (lambda(x): x * f2(a)) in f1(7)" ["y"; "a"];
  (* Note, can't write tests here with decls because in the real compiler
     those should have already been desugared into letrec *)

  tfvs "tfvs_ex_from_notes" "(let rec foo = (lambda(w, x, y, z): (let z = z, y = y, x = x, w = w in (lambda(a): ((a + x) + z)))) in (foo(1, 2, 3, 4))(5))" [];

  tfvs "tfvs_ex_from_notes2" "(lambda(w, x, y, z): (let z = z, y = y, x = x, w = w in (lambda(a): ((a + x) + z))))" [];

  tfvs "tfvs_ex_from_notes3" "(lambda(a): ((a + x) + z))" ["x"; "z"];
  tfvs "free_vars_max_tail_1" "(let rec max = (lambda(x, y): (let y = y, x = x in (if (x > y): x else: (max(y, x))))) in (max(1, 9)))" [];
  tfvs "free_vars_max_tail_1_inner" "(lambda(x, y): (let y = y, x = x in (if (x > y): x else: (max(y, x)))))" ["max"];
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
  tfvs "fvs_let" "let a = c in b + a" "(alet a_4 = c{c; } in (b{b; } + a_4{a_4; }){b; a_4; }){c; b; }\n{c; b; }";
  tfvs "fvs_letrec" "let rec func = (lambda(x,y): if x < a: y else: let tmp = b in tmp * y) in func(1, 2)"
                    "(aletrec func_4 = (lam(x_20, y_21) (alet binop_9 = (x_20{x_20; } < a{a; }){x_20; a; } in (if binop_9{binop_9; }: y_21{y_21; } else: (alet tmp_15 = b{b; } in (tmp_15{tmp_15; } * y_21{y_21; }){y_21; tmp_15; }){y_21; b; }){y_21; binop_9; b; }){y_21; x_20; b; a; }){b; a; } in (func_4{func_4; }(1{}, 2{})){func_4; }){b; a; }\n{b; a; }";
  tfvs "fvs_interfere3" "let x = 3 in (let y = 4 in (x + y))" "(alet x_4 = 3{} in (alet y_8 = 4{} in (x_4{x_4; } + y_8{y_8; }){y_8; x_4; }){x_4; }){}\n{}";
  tfvs "fvs_interfere2b_new" "let x = 3 in ((let y = 4 in y) ; x)" "(alet x_4 = 3{} in (alet y_11 = 4{} in (alet ?desugar_seq_left_2_8 = y_11{y_11; } in (alet ?desugar_seq_right_1_16 = x_4{x_4; } in ?desugar_seq_right_1_16{?desugar_seq_right_1_16; }){x_4; }){y_11; x_4; }){x_4; }){}\n{}";
  tfvs "fvs_from_class"
       "let x = true in
          let y = if true: (let b = 5 in b) else: 6 in
            x"
       "(alet x_4 = true{} in (alet y_8 = (if true{}: (alet b_13 = 5{} in b_13{b_13; }){} else: 6{}){} in x_4{x_4; }){x_4; }){}\n{}";
  tfvs "fvs_from_class_tup"
       "let x = true in
          let y = if true: (let b = (5,) in b[1]) else: 6 in
            x"
       "(alet x_4 = true{} in (alet y_8 = (if true{}: (alet b_13 = (5{}){} in b_13{b_13; }[1{}]{b_13; }){} else: 6{}){} in x_4{x_4; }){x_4; }){}\n{}";

  tcg "color_easy1" "add1(4)" "";
  tcg "color_easy2" "add1(4 + 5)" "";
  tcg "color_easy3" "if true: (1>2) else: (true && false)" "";
  tcg "color_multi_let" "let x=1, y=5, z=true in z" "x_4=>RDX\n\ty_8=>RSI\n\tz_12=>RDI";
  tcg "color_fvs_from_class"
       "let x = true in
          let y = if true: (let b = 5 in b) else: 6 in
            x" "x_4=>RSI\n\tb_13=>RDI\n\ty_8=>RDI";
]