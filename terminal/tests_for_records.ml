open Test_funcs


let test_records_wf = [
  terr "dup_names" "{fieldA = 736, fieldB = true, fieldC = 1 + 2, fieldA = 736}" "" "Record field names must be unique, duplicate found for: fieldA";
]

let test_records_valid = [
  t "dup_names_mixcase" "let a = {fieldA = 736, fieldB = true, fielda = 736} in 8" "" "8";
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
  t "fields_dont_shadow" "let x = 17 in { x = 3, y = x }" "" "{ x = 3, y = 17 }"
]

let tests_for_records = test_records_wf @ test_records_valid @ test_records_anf
