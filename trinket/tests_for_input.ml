open Test_funcs

let tests_for_input = [
  t "positive_input" "input()" "1" "1";
  t "zero_input" "input()" "0" "0";
  t "negative_input" "input()" "-1" "-1";
  (* terr "overflow_input" "input()" "18446744073709551610" "fdsfds"; *)
  (* terr "negative_overflow_input" "input()" "-18446744073709551610" "fdsfds"; *)
  t "true_input" "input()" "true" "true";
  t "false_input" "input()" "false" "false";
  terr "bad_input" "input()" "this_is_bad_input" "";
  terr "bad_input_2" "input()" "this is bad input" "";
]
