open Assembly
open Errors
open Exprs
open Graph
open Printf
open Util

let caller_saved_regs : arg list =
  [ Reg RDI
  ; Reg RSI
  ; Reg RDX
  ; Reg RCX
  ; Reg R8
  ; Reg R9
  ; Reg R10
  ]
;;

let callee_saved_regs : arg list =
  [ Reg R12
  ; Reg R14
  ; Reg RBX
  ]
;;


(* IMPLEMENT THE BELOW *)

let interfere (e : StringSet.t aexpr) (live : StringSet.t) : grapht =
  raise (NotYetImplemented "Generate interference graphs from expressions for racer")
;;

let color_graph (g: grapht) (init_env: arg name_envt) : arg name_envt =
  raise (NotYetImplemented "Implement graph coloring for racer")
;;

let register_allocation (prog: tag aprogram) : tag aprogram * arg name_envt name_envt =
  let gensym =
    let next = ref 0 in
    (fun name ->
      next := !next + 1;
      sprintf "%s_%d" name (!next)) in
  let fv_prog = free_vars_cache prog in
  let rec help_aexpr (body : StringSet.t aexpr) (si : int) (curr_env_name : string) (env : arg name_envt name_envt) : arg name_envt name_envt * int =
    let help_closure (fname : string) (args : string list) (closure_body : StringSet.t aexpr) (fvs : StringSet.t) (closure_si : int) (closure_env : arg name_envt name_envt) : arg name_envt name_envt * int =
      let args_with_idx = List.mapi (fun i arg -> (arg, RegOffset((i + 3) * word_size, RBP))) args in
      let new_sub_env = List.fold_left (fun accum_env cell -> cell :: accum_env) [] args_with_idx in
      let new_sub_env_with_self = (fname, RegOffset(2*word_size, RBP)) :: new_sub_env in
      let free_vars_list = StringSet.elements fvs in
      let num_free_vars = StringSet.cardinal fvs in
      (* Trick, we know the env is a list and lookups will return 1st found, so just add the updated values to the front.
          This new env assumes we have pushed all the closed over values to the stack in order. *)
      let new_sub_env_with_fvs = (List.mapi (fun idx fv -> (fv, RegOffset(~-1 * (1 + idx)*word_size, RBP))) free_vars_list) @ new_sub_env_with_self in
      let new_env = (fname, new_sub_env_with_fvs)::closure_env in
      let (env_with_body_slots, _) = help_aexpr closure_body (num_free_vars + 1) fname new_env in
      (env_with_body_slots, closure_si) in
    match body with
    | ASeq(cexp, aexp, _) ->
        let (lhs_env, lhs_si) = help_cexpr cexp si curr_env_name env in
        help_aexpr aexp lhs_si curr_env_name lhs_env
    | ALet(fname, CLambda(args, body, fvs), let_body, _) ->
        let newenv = add_var_to_env fname (RegOffset(~-si*word_size, RBP)) curr_env_name env in
        let (bindenv, newsi) = help_closure fname args body fvs (si+1) newenv in
        help_aexpr let_body newsi curr_env_name bindenv
    | ALet(sym, bind, body, _) ->
        let newenv = add_var_to_env sym (RegOffset(~-si*word_size, RBP)) curr_env_name env in
        let (bindenv, newsi) = help_cexpr bind (si+1) curr_env_name newenv in
        help_aexpr body newsi curr_env_name bindenv
    | ALetRec((fname, CLambda(args, body, fvs))::bindings, let_rec_body, let_rec_fvs) ->
        (*let (bindings_env, bindings_si) =
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
        help_aexpr body new_si curr_env_name new_env*)
        let newenv = add_var_to_env fname (RegOffset(~-si*word_size, RBP)) curr_env_name env in
        let (bindenv, newsi) = help_closure fname args body fvs (si+1) newenv in
        (help_aexpr (ALetRec(bindings, let_rec_body, let_rec_fvs)) newsi curr_env_name bindenv)
    | ALetRec([], body, _) -> help_aexpr body si curr_env_name env
    | ALetRec _ -> raise (InternalCompilerError "LetRecs cannot have non-CLambda bindings")
    | ACExpr(cexpr) -> help_cexpr cexpr si curr_env_name env
  and help_cexpr (expr : StringSet.t cexpr) (si : int) (curr_env_name : string) (env : arg name_envt name_envt) : arg name_envt name_envt * int =
    match expr with
    | CIf(cond, lhs, rhs, _) ->
        let (lhs_env, lhs_si) = help_aexpr lhs si curr_env_name env in
        help_aexpr rhs lhs_si curr_env_name lhs_env
    | CScIf(cond, lhs, rhs, _) ->
        let (lhs_env, lhs_si) = help_aexpr lhs si curr_env_name env in
        help_aexpr rhs lhs_si curr_env_name lhs_env
    | CPrim1 _ -> (env, si)
    | CPrim2 _ -> (env, si)
    | CApp _ -> (env, si)
    | CImmExpr _ -> (env, si)
    | CTuple _ -> (env, si)
    | CGetItem _ -> (env, si)
    | CSetItem _ -> (env, si)
    | CLambda(_, _, _) -> raise (InternalCompilerError ("CLambda allocation should be handled by specific help_aexpr ALet/ALetRec cases"))
  in
  match fv_prog with
  | AProgram(aexp, fvs) ->
      let (out, _) = help_aexpr aexp 1 "?our_code_starts_here" [("?our_code_starts_here", [])] in
        (prog, out)
