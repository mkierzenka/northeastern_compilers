open Test_funcs

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
  (*t "lambda_seq_right" "8;(lambda(x): x + 5)" "" "<function arity 1, fn-ptr 0x401f70, closed 0>";*)

  tint "interfere1" "let a = 3 in a" "";
  tint "interfere2a" "let x = 3, y = 4 in x" "x_4: y_8\ny_8: x_4";
  tint "interfere2b" "let x = 3, y = 4 in y" "x_4: y_8\ny_8: x_4";
  tint "interfere2b_new" "let x = 3 in ((let y = 4 in y) ; x)" "?desugar_seq_left_2_8: y_11, x_4, ?desugar_seq_right_1_16\n?desugar_seq_right_1_16: y_11, x_4, ?desugar_seq_left_2_8\nx_4: y_11, ?desugar_seq_right_1_16, ?desugar_seq_left_2_8\ny_11: x_4, ?desugar_seq_right_1_16, ?desugar_seq_left_2_8";

  tint "interfere3a" "let x = 3, y = 4 in (x + y)" "x_4: y_8\ny_8: x_4";
  tint "interfere3b" "let x = 3 in (let y = 4 in (x + y))" "x_4: y_8\ny_8: x_4";
  tint "interfere_from_class"
       "let x = true in
          let y = if true: (let b = 5 in b) else: 6 in
            x"
       "b_13: x_4\nx_4: y_8, b_13\ny_8: x_4";
  
  terr "seq_desugar" "(let x = 3 in true); x" "" "The identifier x, used at <seq_desugar, 1:21-1:22>, is not in scope";
]

let racer_tr = [
  tr "reg_let1" "let a = input(), b=4*5 in (if a > b: false else: a + a)" "444" "false";
]

let tests_from_racer = pair_tests @ (* oom @ gc @ *) input @ racer (*@ fvs_tests*) (* @ racer_tr *)
