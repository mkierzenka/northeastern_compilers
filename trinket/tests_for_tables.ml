open Test_funcs

let valid_tables = [
  t "empty" "(| |)" "" "(empty table)";
  t "empty_recs" "(| {}, {}, {}, {} |)" "" "table:\n\t(no fields)\n0\t\n1\t\n2\t\n3\t";
  t "one_empty_rec" "(| { test = {} }, { test = { inner = true } } |)" "" "table:\n\ttest\n0\t{}\n1\t{ inner = true }";
  t "basic" "let val = 7, mytrue = true, myfalse = false in (| {c1 = 3, c2 = myfalse}, {c1 = val, c2 = (myfalse || mytrue)}, {c1 = input(), c2 = -1} |)" "999" "table:\n\tc1\tc2\n0\t3\tfalse\n1\t7\ttrue\n2\t999\t-1";
  t "eq_operator" "let tab1 = (| {a=1, b=2}, {a=3, b=4} |), tab2 = tab1, tab3 = (| {a=1, b=2}, {a=3, b=4} |) in print(tab1 == tab1); print(tab1 == tab2); (tab1 == tab3)" "" "true\ntrue\nfalse";
  t "check_istable" "let tab1 = (| {a=1, b=2}, {a=3, b=4} |), empty = (| |) in print(istable(tab1)); print(istable(empty)); print(istable({ a=1, b=2})); print(istable(-88)); istable((lambda (a): empty))" "" "true\ntrue\nfalse\nfalse\nfalse";
  t "other_typechecks" "let tab1 = (| {a=1, b=2}, {a=3, b=4} |), empty = (| |) in
                        print(istuple(tab1)); print(istuple(empty)); print(isrecord(tab1)); print(isrecord(empty)); isbool(tab1)"
                      ""  "false\nfalse\nfalse\nfalse\nfalse";
  t "equal" "let tab1 = (| {a=1, b=2}, {a=3, b=4} |), tab2 = tab1, tab3 = (| {a=1, b=2}, {a=3, b=4} |) in print(equal(tab1, tab1)); print(equal(tab2, tab1)); print(equal(tab1, tab3)); equal(tab3, tab1)" "" "true\ntrue\ntrue\ntrue";
  t "unequal_values" "let tab1 = (| {a=1, b=2}, {a=3, b=4} |), tab1small = (| {a=1}, {a=3} |),
                          tab1a = (| {a=-9, b=2}, {a=3, b=4} |), tab1b = (| {a=1, b=1000}, {a=3, b=4} |),
                          tab1c = (| {a=1, b=2}, {a=false, b=4} |), tab1d = (| {a=1, b=2}, {a=3, b=444} |) in
                        print(equal(tab1, 1)); print(equal(tab1, {a=1, b=2})); print(equal(tab1, tab1small)); print(equal(tab1, tab1a));
                        print(equal(tab1, tab1b)); print(equal(tab1, tab1c)); equal(tab1, tab1d)"
                      "" "false\nfalse\nfalse\nfalse\nfalse\nfalse\nfalse";
  t "unequal_nested" "let func1 = (lambda (x): (4 - 2)), tab1 = (| {a=1, b=func1}, {a=3, b={other=77}} |), tab2 = tab1, tab3 = (| {a=1, b=func1}, {a=3, b={other=-1}} |) in print(equal(tab1, tab3)); equal(tab3, tab1)" "" "false\nfalse";
  t "unequal_fieldids" "let tab1 = (| {a=1, b=2}, {a=3, b=4} |), tab2 = (| {aa=1, bb=2}, {aa=3, bb=4} |) in equal(tab1, tab2)" "" "false";
]

let invalid_tables = [
  terr "inconsistent_cols" "let rec1 = {aaa=73847} in (| rec1, {bbb=73847} |)" "" "table-create expected homogeneous records. Inconsistent record was { bbb = 73847 }";
  terr "inconsistent_cols_partial1" "let rec1 = {aa = 11, bb = (false && true)}, rec2 = {aa = 9, bb = true} in (| rec1, rec2, {bb = false} |)" "" "table-create expected homogeneous records. Inconsistent record was { bb = false }";
  terr "inconsistent_cols_partial2" "let rec1 = {aa = 11, bb = (false && true)}, rec2 = {aa = 9, bb = true} in (| rec1, rec2, {aa = 10} |)" "" "table-create expected homogeneous records. Inconsistent record was { aa = 10 }";
  terr "inconsistent_cols_partial3" "let rec1 = {aa = 11, bb = (false && true)}, rec2 = {aa = 9, bb = true} in (| rec1, rec2, { } |)" "" "table-create expected homogeneous records. Inconsistent record was {}";
  terr "inconsistent_cols_empty" "if true: (| {}, {aa = true} |) else: 3" "" "table-create expected homogeneous records. Inconsistent record was { aa = true }";

  terr "non_record_num" "let rec1 = {aaa=73847} in (| rec1, 333 |)" "" "table-create expected record, got 333";
  terr "non_record_bool" "let rec1 = {aaa=false} in (| rec1, true |)" "" "table-create expected record, got true";
  terr "non_record_closure" "let rec1 = {aaa=input()}, func1 = (lambda (x, y): (x + y)) in (| rec1, rec1, func1 |)" "73847" "table-create expected record, got";
  terr "non_record_table" "let rec1 = {aaa=73847}, othertable = (| rec1 |) in (| rec1, othertable |)" "" "table-create expected record, got table:\n\taaa\n0\t73847";
]

let tests_for_tables = valid_tables @ invalid_tables
