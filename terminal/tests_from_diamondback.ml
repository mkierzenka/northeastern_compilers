open Test_funcs

(* ### Regression test suite (from Diamondback) ### *)
let multi_errs_code_str = "def f(x, x): y  f(1)"

let tests_from_diamondback = [
  (* ** Functions ** *)
  t "func_not_used_1" "def t(): true true"  "" "true";
  t "func_not_used_2" "def t(): true false"  "" "false";
  t "func_not_used_3" "def t(): 1 23"  "" "23";
  t "func_not_used_4" "def t(): if true: 88 else: 92 -3"  "" "-3";
  t "func_not_used_1a" "def id(x): x 10"  "" "10";
  t "func_not_used_2a" "def id(x): x true"  "" "true";
  t "func_not_used_3a" "def func(x): add1(x) true"  "" "true";
  t "func_not_used_4a" "def func(x): (2 + x) true"  "" "true";
  t "func_not_used_5a" "def func(x): if x < 2: 0 else: 1 8"  "" "8";
  t "multiple_func_not_used" "def a(): 2 def ident(x): x def cat(x): print(x) 8"  "" "8";
  t "func_group_not_used" "def a(): 2 and def ident(x): x and def cat(x): print(x) 8"  "" "8";
  t "func_unused_args" "def fun(x, y, z): print(y) 8"  "" "8";

  (* Calling funcs *)
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

  terr "fname_bind_in_body" "def fun(a,b,c): let fun=4 in add1(fun) \n fun(9,10,11)"  "" "shadows one";
  t "func_split_env" "def f(x,y): let z = x * y in sub1(z)   let z = 9 in f(z, add1(z))" ""  "89";
  t "func_from_func" "def f(x,y): let z = x * y in z + z  and def g(x): if isbool(x): 0 else: f(x,x) g(4)"  "" "32";
  terr "func_from_nonpreceding_func_dif_grp" "def g(x): if isbool(x): 0 else: f(x,x)  def f(x,y): let z = x * y in z + z g(4)"  "" "The identifier f";
  t "func_from_func_backwards" "def f(): g()  and def g(): sub1(2 * 8)  f()"  "" "15";
  terr "func_from_func_backwards_dif_grp" "def f(): g()  def g(): sub1(2 * 8)  f()"  "" "The identifier g";
  t "max_tail_1" "def max(x,y): if x > y: x else: max(y,x) max(1,9)"  "" "9";
  t "max_tail_2" "def max(x,y): if x > y: x else: max(y,x) max(9,1)"  "" "9";
  terr "rebind_arg" "def f(a,b): let a=b,b=8 in a+b f(4,10)"  "" "shadows one";

  (* tail call testing *)
  t "tail_larger_arity_2_to_3" "def f(x,y): g(x,y,4) and def g(a,b,c): a - b + c  f(2,5)"  "" "1";
  t "tail_larger_arity_3_to_4" "def f(x,y,z): g(x,4,z,y) and def g(a,b,c,d): a - b + c - d  f(1,2,3)"  "" "-2";
  t "tail_larger_arity_2_to_4" "def f(x,y): g(x,-9, y,4) and def g(a,b,c,d): a - b + c - d  f(2,5)"  "" "12";
  t "tail_same_arity_1" "def f(x): g(x + 8) and def g(x): x - 2  f(4)"  "" "10";
  t "tail_same_arity_2" "def f(x,y): g(sub1(x),add1(y)) and def g(x,y): x * y  f(3,5)"  "" "12";
  t "tail_same_arity_3" "def g(a,b,c): (a + b) * c  def f(x,y,z): g(x,z,y)  f(2,2,4)" ""  "12";
  t "tail_smaller_arity_3_to_2" "def g(i,k): i * k  and def f(i,j,k): g(i+j,k)  f(0,2,2)" ""  "4";
  t "tail_smaller_arity_4_to_3" "def f(i,j,k,hi): g(i+j,k*hi,hi) and def g(i,k,x): x + (i*k)  f(0,2,2,1)"  "" "5";
  t "tail_smaller_arity_4_to_2" "def f(i,j,k,hi): g(i+j,k*hi) and def g(i,k): 3 + (i*k)  f(0,2,2,1)"  "" "7";

  (* Asserting that functions don't leak envs *)
  terr "func_split_env_err" "def f(x,y): let z = x * y in sub1(z)   let z = 9 in f(x, add1(z))"  "" "is not in scope";
  terr "func_split_env_err2a" "def f(x,y): let z = x * y in sub1(z)   let a = f(1, 2) in z"  "" "is not in scope";
  terr "func_split_env_err2b" "def f(x,y): let z = x * y in sub1(z)   let a = f(1, 2) in y" ""  "is not in scope";
  terr "func_split_env_err3" "def f(x,y): sub1(z)   let z=1 in f(1, 2)" ""  "is not in scope";
  terr "func_split_env_err4a" "def f(x,y): let z=99 in x+y  def g(x): print(z)   8"  "" "is not in scope";
  terr "func_split_env_err4b" "def f(x,y): let z=99 in x+y  def g(x): print(z)   let one=f(1,2) in g(3)"  "" "is not in scope";
  terr "func_split_env_err4c" "def f(x,y): let z=99 in x+y  z"  "" "is not in scope";
  terr "func_split_env_err4d" "def f(x,y): let z=99 in x+y  def g(w): print(x)   let one=f(1,2) in f(1,2)" ""  "is not in scope";

  (* Arity errors *)
  terr "arity_err0a" "def f(x): 2 f(4,5)"  "" "expected an arity of 1, but received 2 arguments";
  terr "arity_err0b" "def f(): (if isnum(12): 7 else: false)  f(4)"  "" "expected an arity of 0, but received 1 arguments";
  terr "arity_err1a" "def f(x): (if isnum(12): x else: false)  f()" ""  "expected an arity of 1, but received 0 arguments";
  terr "arity_err1b" "def f(x): (if isnum(12): x else: false)  f(4,8)"  "" "expected an arity of 1, but received 2 arguments";
  terr "arity_err2a" "def f(x,y): (if isnum(12): 7 else: false)  f(1)"  "" "expected an arity of 2, but received 1 arguments";
  terr "arity_err2b" "def f(x,y): (if isnum(12): 7 else: false)  f(1,3,4)"  "" "expected an arity of 2, but received 3 arguments";

  (* Name resolution for vars vs. funcs (vars shadow function names) *)
  terr "func_let_name_l" "def f(x,y): (if isnum(12): 7 else: false)  let f=99 in f(1,3)"  "" "The identifier f";
  terr "func_let_name_r" "def f(x,y): (if isnum(12): 7 else: false)  let f=99 in f(1,3)"  "" "shadows one";
  terr "func_let_name2" "def f(x,y): (if isnum(12): 7 else: false)  let f=99 in f(1,3,4)"  "" "shadows one";
  terr "func_let_name3" "def f(x,y): (if isnum(12): 7 else: false)  let f=99 in add1(f)" ""  "shadows one";


  (* UnboundFun errors *)
  terr "unbound_fun_l" "f()"  "" "The identifier f, used at";
  terr "unbound_fun_r" "f()"  "" ", is not in scope";
  terr "unbound_fun" "def f(): add1(4 * 2)  def g(): sub1(2 * 8)  if false: h() else: 9" ""  "is not in scope";
  terr "unbound_fun_in_decl" "def f(): add1(4 * 2)  def g(): h()  7"  "" "not in scope";
  terr "unbound_fun_let" "def f(): add1(4 * 2)  def g(): sub1(2 * 8) let h=true in h()"  "" "tried to call a non-closure value";

  (* UnboundId errors *)
  terr "unbound_id_l" "a"  "" "The identifier a, used at";
  terr "unbound_id_r" "a" ""  ", is not in scope";
  terr "unbound_id" "def id(y): y  let x=1 in y"  "" "is not in scope";
  terr "unbound_id_if" "if false: z else: 7" ""  "is not in scope";
  terr "unbound_arg" "def f(x, y): z  8"  "" "is not in scope";
  terr "unbound_arg2" "def f(x, y): x+y def g(a): z  8"  "" "is not in scope";
  terr "unbound_id_call" "def f(x, y): let z=y in add1(x + z)  isnum(f(3,a))"  "" "is not in scope";

  (* DuplicateId errors *)
  terr "duplicate_id_l" "let x=1,x=2 in 3" ""  "The identifier x, redefined at";
  terr "duplicate_id_r" "let x=1,x=2 in 3"  "" ", duplicates one at";

  (* DuplicateFun errors *)
  terr "duplicate_fun_l" "def f(): 2 def f(): 3 8"  "" "The function name f, redefined at";
  terr "duplicate_fun_r" "def f(): 2 def f(): 3 8"  "" ", duplicates one at";
  terr "duplicate_fun_2_l" "def f(a,b): 2 def f(): 3 8"  "" "The function name f, redefined at";
  terr "duplicate_fun_2_r" "def f(a,b): 2 def f(): 3 8"  "" ", duplicates one at";
  terr "duplicate_fun_3" "def f(): 2 and def g(): 1 and def f(): 3   8"  "" "duplicate";

  (* Overflow errors were tested in Cobra *)

  (* Multiple errors *)
  terr "unbound_duplicate_id_unbl" "let x=1,x=2 in y"  "" "The identifier y, used at";
  terr "unbound_duplicate_id_unbr" "let x=1,x=2 in y"  "" ", is not in scope";
  terr "unbound_duplicate_id_dupl" "let x=1,x=2 in y"  "" "The identifier x, redefined at";
  terr "unbound_duplicate_id_dupr" "let x=1,x=2 in y"  "" ", duplicates one at";

  terr "multi_errs_unbound_l" multi_errs_code_str "" "The identifier y, used at ";
  terr "multi_errs_unbound_r" multi_errs_code_str "" ", is not in scope";
  terr "multi_errs_duplicated_l" multi_errs_code_str "" "The identifier x, redefined at ";
  terr "multi_errs_duplicated_r" multi_errs_code_str "" ", duplicates one at ";
]