open Printf
(* open Pretty
open Phases *)
open Exprs
open Assembly
open Errors
open Util

(* TODO- explain/justify our env choice (see assignment) *)
(* ASSUMES that the program has been alpha-renamed and all names are unique *)
let naive_stack_allocation (prog: tag aprogram) : tag aprogram * arg name_envt name_envt * int name_envt =
  let rec help_aexpr (body : tag aexpr) (si : int) (curr_env_name : string) (env : arg name_envt name_envt) (field_nums : int name_envt) : arg name_envt name_envt * int name_envt * int =
    let help_closure (fname : string) (args : string list) (closure_body : tag aexpr) (closure_tag : tag) (closure_si : int) (closure_env : arg name_envt name_envt) (closure_field_nums : int name_envt): arg name_envt name_envt * int name_envt * int =
      let args_with_idx = List.mapi (fun i arg -> (arg, RegOffset((i + 3) * word_size, RBP))) args in
      let new_sub_env = List.fold_left (fun accum_env cell -> cell :: accum_env) [] args_with_idx in
      let new_sub_env_with_self = (fname, RegOffset(2*word_size, RBP)) :: new_sub_env in
      let free_vars_list = List.sort String.compare (free_vars (ACExpr(CLambda(args, closure_body, closure_tag)))) in
      let num_free_vars = List.length free_vars_list in
      (* Trick, we know the env is a list and lookups will return 1st found, so just add the updated values to the front.
          This new env assumes we have pushed all the closed over values to the stack in order. *)
      let new_sub_env_with_fvs = (List.mapi (fun idx fv -> (fv, RegOffset(~-1 * (1 + idx)*word_size, RBP))) free_vars_list) @ new_sub_env_with_self in
      let new_env = (fname, new_sub_env_with_fvs)::closure_env in
      let (env_with_body_slots, new_field_nums, _) = help_aexpr closure_body (num_free_vars + 1) fname new_env closure_field_nums in
      (env_with_body_slots, new_field_nums, closure_si) in
    match body with
    | ASeq(cexp, aexp, _) ->
        let (lhs_env, lhs_field_nums, lhs_si) = help_cexpr cexp si curr_env_name env field_nums in
        help_aexpr aexp lhs_si curr_env_name lhs_env lhs_field_nums
    | ALet(fname, CLambda(args, body, ctag), let_body, _) ->
        let newenv = add_var_to_env fname (RegOffset(~-si*word_size, RBP)) curr_env_name env in
        let (bindenv, new_field_nums, newsi) = help_closure fname args body ctag 1 newenv field_nums in
        help_aexpr let_body (si + 1) curr_env_name bindenv new_field_nums
    | ALet(sym, bind, body, _) ->
        let newenv = add_var_to_env sym (RegOffset(~-si*word_size, RBP)) curr_env_name env in
        let (bindenv, bind_field_nums, newsi) = help_cexpr bind (si+1) curr_env_name newenv field_nums in
        help_aexpr body newsi curr_env_name bindenv bind_field_nums
    | ALetRec((fname, CLambda(args, body, ctag))::bindings, let_rec_body, let_rec_tag) ->
        let newenv = add_var_to_env fname (RegOffset(~-si*word_size, RBP)) curr_env_name env in
        let (bindenv, bind_field_nums, _) = help_closure fname args body ctag 1 newenv field_nums in
        (help_aexpr (ALetRec(bindings, let_rec_body, let_rec_tag)) (si + 1) curr_env_name bindenv bind_field_nums)
    | ALetRec([], body, _) -> help_aexpr body si curr_env_name env field_nums
    | ALetRec _ -> raise (InternalCompilerError "LetRecs cannot have non-CLambda bindings")
    (* | ALetRec(bindings, body, _) ->
      let (bindings_env, bindings_si) =
        List.fold_left (
          fun (accum_env, accum_si) (name, _) ->
            (add_var_to_env name (RegOffset(~-accum_si*word_size, RBP)) curr_env_name accum_env, accum_si + 1)
        )
        (env, si) bindings in
      let (new_env, new_si) =
        List.fold_left (fun (accum_env, accum_si) (_, exp) ->
          help_cexpr exp accum_si curr_env_name accum_env)
        (bindings_env, bindings_si)
        bindings in
      help_aexpr body new_si curr_env_name new_env *)
    | ACExpr(cexpr) -> help_cexpr cexpr si curr_env_name env field_nums
  and help_cexpr (expr : tag cexpr) (si : int) (curr_env_name : string) (env : arg name_envt name_envt) (field_nums : int name_envt) : arg name_envt name_envt * int name_envt * int =
    match expr with
    | CIf(cond, lhs, rhs, _) ->
        let (lhs_env, lhs_field_nums, lhs_si) = help_aexpr lhs si curr_env_name env field_nums in
        help_aexpr rhs lhs_si curr_env_name lhs_env lhs_field_nums
    | CScIf(cond, lhs, rhs, _) ->
        let (lhs_env, lhs_field_nums, lhs_si) = help_aexpr lhs si curr_env_name env field_nums in
        help_aexpr rhs lhs_si curr_env_name lhs_env lhs_field_nums
    | CPrim1 _ -> (env, field_nums, si)
    | CPrim2 _ -> (env, field_nums, si)
    | CApp _ -> (env, field_nums, si)
    | CImmExpr _ -> (env, field_nums, si)
    | CTuple _ -> (env, field_nums, si)
    | CGetItem _ -> (env, field_nums, si)
    | CSetItem _ -> (env, field_nums, si)
    | CLambda(_, _, _) -> raise (InternalCompilerError ("CLambda allocation should be handled by specific help_aexpr ALet/ALetRec cases"))
    | CRecord(bindings, _) ->
      let new_field_nums =
        List.fold_left (
          fun (field_nums_acc) (name, _) ->
            match field_nums_acc with
            | [] -> [(name, 0)]
            | (_, max_so_far)::_ ->
                if List.mem_assoc name field_nums_acc
                then field_nums_acc
                else (name, max_so_far + 1)::field_nums_acc
        ) field_nums bindings in
      (env, new_field_nums, si)
    | CGetField(_, _, _) -> (env, field_nums, si)
  in
  match prog with
  | AProgram(aexp, tag) ->
      let (out_env, out_field_nums, _) = help_aexpr aexp 1 "?our_code_starts_here" [("?our_code_starts_here", [])] [] in
        (prog, out_env, out_field_nums)
