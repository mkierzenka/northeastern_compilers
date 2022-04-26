open Test_funcs

let tests_from_fdl = [
  terr "letrec_non_lam" "let rec a=(lambda(x): x*x), (b,c)=(1,2) in 4" "" "err";
  terr "call_num" "let f=7 in f()" "" "non-closure";
  terr "letrec_dups" "let rec a=(lambda(x): x*x), b=(lambda(x): 2*x), a=(lambda(x): 444) in 7" "" "duplicate";

  t "decls_grouped_pass" "def f1(x): if x > 0: g1(x) else: x and def g1(y): f1(y - 2) f1(5)" "" "-1";
  terr "decls_ungrouped_fail" "def f2(x): if x > 0: g2(x) else: x     def g2(y): f2(y - 2) f2(5)" "" "The identifier g2";
  t "decls_ungrouped_pass" "def a3(x): 3   def b3(y): a3(y) b3(7)" "" "3";
]
