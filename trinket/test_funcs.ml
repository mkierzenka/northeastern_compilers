open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors
open Anf
open Util
open Graph
open Register_allocation
open Desugar
open Rename_and_tag

let t name program input expected = name>::test_run ~args:[] ~std_input:input Naive program name expected;;
let tr name program input expected = name>::test_run ~args:[] ~std_input:input Register program name expected;;
let ta name program input expected = name>::test_run_anf ~args:[] ~std_input:input program name expected;;
let tgc name heap_size program input expected = name>::test_run ~args:[string_of_int heap_size] ~std_input:input Naive program name expected;;
let tvg name program input expected = name>::test_run_valgrind ~args:[] ~std_input:input Naive program name expected;;
let tvgc name heap_size program input expected = name>::test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input Naive program name expected;;
let terr name program input expected = name>::test_err ~args:[] ~std_input:input Naive program name expected;;
let tgcerr name heap_size program input expected = name>::test_err ~args:[string_of_int heap_size] ~std_input:input Naive program name expected;;
let tanf name program input expected = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

let tparse name program expected = name>::fun _ ->
  assert_equal (untagP expected) (untagP (parse_string name program)) ~printer:string_of_program;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

(* let tfvs name program expected = name>:: *)
(*   (fun _ -> *)
(*     let ast = parse_string name program in *)
(*     let anfed = anf (tag ast) in *)
(*     let vars = free_vars_P anfed [] in *)
(*     let c = Stdlib.compare in *)
(*     let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in *)
(*     assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print) *)
(* ;; *)

let tfvs name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let desug = desugar ast in
    let tagged = tag desug in
    let renamed = rename_and_tag tagged in
    let anfed = anf (tag renamed) in
    let fv_prog = free_vars_cache anfed in
    assert_equal expected (string_of_aprogram_with_fvs fv_prog) ~printer:(fun s -> s))

let tint name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let desug = desugar ast in
    let tagged = tag desug in
    let renamed = rename_and_tag tagged in
    let anfed = anf (tag renamed) in
    let fv_prog = free_vars_cache anfed in
    let int =
      match fv_prog with
      | AProgram(body, _) -> interfere body StringSet.empty in
    assert_equal expected (string_of_graph int) ~printer:(fun s -> s))

let tcg name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let desug = desugar ast in
    let tagged = tag desug in
    let renamed = rename_and_tag tagged in
    let anfed = anf (tag renamed) in
    let fv_prog = free_vars_cache anfed in
    let int =
      match fv_prog with
      | AProgram(body, _) -> interfere body StringSet.empty in
    let coloring = color_graph int [] in
    assert_equal expected (string_of_arg_env coloring) ~printer:(fun s -> s))