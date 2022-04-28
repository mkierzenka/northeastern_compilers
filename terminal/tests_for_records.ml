open Test_funcs


let test_records_wf = [
  terr "dup_names" "{fieldA = 736, fieldB = true, fieldC = 1 + 2, fieldA = 736}" "" "Record field names must be unique, duplicate found for: fieldA";
]

let test_records_valid = [
  t "dup_names_mixcase" "let a = {fieldA = 736, fieldB = true, fielda = 736} in 8" "" "8";
]

let tests_for_records = test_records_wf @ test_records_valid