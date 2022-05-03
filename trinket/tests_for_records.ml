open Test_funcs


let test_records_wf = [
  terr "dup_names" "{fieldA = 736, fieldB = true, fieldC = 1 + 2, fieldA = 736}" "" "The field fieldA, redefined at <dup_names, 1:46-1:52>, duplicates one at <dup_names, 1:1-1:7>";
  terr "shadow" "let a = 5 in { x = (let a = 3 in a) }" "" "The identifier a, defined at <shadow, 1:24-1:25>, shadows one defined at <shadow, 1:4-1:5>";
]

let test_records_valid = [
  t "basic" "{a=1234, b=(if input() < 990: 990 * 2 else: -100 ), c=(false && 7)}" "8" "{ a = 1234, b = 1980, c = false }";
  t "nested" "{outerfield = -12, nest={innerfield=9000, if2=false}}" "" "{ outerfield = -12, nest = { innerfield = 9000, if2 = false } }";
  t "dup_names_mixcase" "let a = {fieldA = 736, fieldB = true, fielda = 736} in 8" "" "8";
  t "let_field" "let var=160, rec1 = {f1 = var}, rec2 = {inner = rec1} in (rec1 == rec2) || (var == rec1)" "" "false";
  t "ok_shadow" "let a = 5 in { a = 3 }" "" "{ a = 3 }";
  t "inner_shadow" "{ a = { a = 3 } }" "" "{ a = { a = 3 } }";
  t "raw_equal" "let a = {f1=-100, f2=-99, f3=-98, f4=-97},
                     a_alias = a, a_copy = {f1=a.f1, f2=a.f2, f3=a.f3, f4=a.f4},
                     a_almost = {f1=a.f1, f2=a.f2, f3=a.f3, f4=a.f4 + 1}
                 in (a == a) && (a == a_alias) && !(a == a_copy) && !(a == a_almost) && !({blah = 44} == 44)"
                "" "true";
]

let test_records_anf = [
  (* { x = print(3), y = 5 } =>
  LetRec([
        ("?rec_0_field_1_y", ImmNum(5)),
        ("?rec_0_field_0_x", Prim1(Print, ImmNum(3)))
      ],
      Record([("y", ImmId("?rec_0_field_1_y")), ("x", ImmId("?rec_0_field_0_x"))])
  ) *)
  t "rec_anf1" "{ x = print(3), y = 5 }" "" "3\n{ x = 3, y = 5 }";
  (* let x = 17 in { x = 3, y = x } =>
  Let("x", ImmNum(17),
      LetRec([
        ("?rec_0_field_1_y", ImmId("x")),
        ("?rec_0_field_0_x", ImmNum(17))
      ])
  ) *)
  terr "no_field_ref" "{ x = 3, y = x }" "" "The identifier x, used at <no_field_ref, 1:13-1:14>, is not in scope";
  t "fields_dont_shadow" "let x = 17 in { x = 3, y = x }" "" "{ x = 3, y = 17 }";
]

(*

let a = (1, 2, 3),
    test = 1 in
    {test = true}.test


add test(s) to show left associative field access, not right associative

*)

let tests_for_records = test_records_wf @ test_records_valid @ test_records_anf
