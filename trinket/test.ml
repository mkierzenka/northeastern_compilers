open OUnit2
open Runner
open Test_funcs
open Tests_from_cobra
open Tests_from_diamondback
open Tests_from_eggeater
open Tests_from_fdl
open Tests_from_racer
open Tests_for_records
open Tests_for_tables
open Tests_for_input


let cobra_suite = "cobra_suite">:::tests_from_cobra
let diamondback_suite = "diamondback_suite">:::tests_from_diamondback
let eggeater_suite = "eggeater_suite">:::tests_from_eggeater
let fdl_suite = "fdl_suite">:::tests_from_fdl
let racer_suite = "racer_suite">:::tests_from_racer
let records_suite = "records_suite">:::tests_for_records
let tables_suite = "tables_suite">:::tests_for_tables
let input_suite = "input_suite">:::tests_for_input
(* TODO- figure out and add tests_free_vars.ml *)


let () =
  run_test_tt_main ("all_tests">:::[
    cobra_suite;
    diamondback_suite;
    eggeater_suite;
    fdl_suite;
    racer_suite;
    records_suite;
    tables_suite;
    input_suite;
    input_file_test_suite ();
  ])
;;
