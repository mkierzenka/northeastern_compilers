open Test_funcs

let valid_tables = [
  t "empty" "(| |)" "" "(empty table)";
  (* t "empty_recs" "(| {} {} {} {} |)" "" "zz"; *)
  t "basic" "let val = 7, mytrue = true, myfalse = false in (| {c1 = 3, c2 = myfalse}, {c1 = val, c2 = (myfalse || mytrue)}, {c1 = input(), c2 = -1} |)" "999" "table:\n\tc1\tc2\n0\t3\tfalse\n1\t7\ttrue\n2\t999\t-1";
  t "eq_operator" "let tab1 = (| {a=1, b=2}, {a=3, b=4} |), tab2 = (| {a=1, b=2}, {a=3, b=4} |) in print(tab1 == tab1); (tab1 == tab2)" "" "true\nfalse";
  t "checking_types" "let tab1 = (| {a=1, b=2}, {a=3, b=4} |), empty = (| |) in
                        print(istuple(tab1)); print(istuple(empty)); print(isrecord(tab1)); print(isrecord(empty)); isbool(tab1)"
                      ""  "false\nfalse\nfalse\nfalse\nfalse";
]

let invalid_tables = [
  terr "inconsistent_cols" "let rec1 = {aaa=73847} in (| rec1, {bbb=73847} |)" "" "table-create expected homogeneous records. Inconsistent record was { bbb = 73847 }";
  terr "inconsistent_cols_partial1" "let rec1 = {aa = 11, bb = (false && true)}, rec2 = {aa = 9, bb = true} in (| rec1, rec2, {bb = false} |)" "" "table-create expected homogeneous records. Inconsistent record was { bb = false }";
  terr "inconsistent_cols_partial2" "let rec1 = {aa = 11, bb = (false && true)}, rec2 = {aa = 9, bb = true} in (| rec1, rec2, {aa = 10} |)" "" "table-create expected homogeneous records. Inconsistent record was { aa = 10 }";
  (*terr "inconsistent_cols_partial3" "let rec1 = {aa = 11, bb = (false && true)}, rec2 = {aa = 9, bb = true} in (| rec1, rec2, { } |)" "" "table-create expected homogeneous records. Inconsistent record was {}";*)
  (*terr "inconsistent_cols_empty" "if true: (| {}, {aa = true} |)" "" "zz";*)

  terr "non_record_num" "let rec1 = {aaa=73847} in (| rec1, 333 |)" "" "table-create expected record, got 333";
  terr "non_record_bool" "let rec1 = {aaa=false} in (| rec1, true |)" "" "table-create expected record, got true";
  terr "non_record_closure" "let rec1 = {aaa=input()}, func1 = (lambda (x, y): (x + y)) in (| rec1, rec1, func1 |)" "73847" "table-create expected record, got";
  terr "non_record_table" "let rec1 = {aaa=73847}, othertable = (| rec1 |) in (| rec1, othertable |)" "" "table-create expected record, got table:\n\taaa\n0\t73847";
]

let tests_for_tables = valid_tables @ invalid_tables
