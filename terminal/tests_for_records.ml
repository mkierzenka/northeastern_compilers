open Test_funcs


let test_records_wf = [
  terr "dup_names" "{fieldA = 736, fieldB = true, fieldC = 1 + 2, fieldA = 736}" "" "Record field names must be unique, duplicate found for: fieldA";
  terr "shadow" "let a = 5 in { x = (let a = 3 in a) }" "" "??shadow";
]

let test_records_valid = [
  t "basic" "{a=1234, b=(if input() < 990: 990 / 2 else: -100 ), c=(false && 7)}" "8" "{a=1234, b=495, c=false}";
  t "nested" "{outerfield = -12, nest={innerfield=9000, if2=false}}" "" "{outerfield=-12, nest ={innerfield=9000, if2=false}}";
  t "dup_names_mixcase" "let a = {fieldA = 736, fieldB = true, fielda = 736} in 8" "" "8";
  t "let_field" "let var=160, rec1 = {f1 = var}, rec2 = {inner = rec1} in (rec1 == rec2) || (var == rec1)" "" "false";
  t "ok_shadow" "let a = 5 in { a = 3 }" "" "{a = 3}";
  t "inner_shadow" "{ a = { a = 3 } }" "" "{a = {a = 3}}"
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
  terr "no_field_ref" "{ x = 3, y = x }" "" "Unbound id";
  t "fields_dont_shadow" "let x = 17 in { x = 3, y = x }" "" "{ x = 3, y = 17 }";
]

let tests_for_records = test_records_wf @ test_records_valid @ test_records_anf
