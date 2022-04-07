open Printf
(* open Pretty
open Phases *)
open Exprs
open Assembly
(* open Errors *)
open Util

(* ASSUMES that the program has been alpha-renamed and all names are unique *)
let naive_stack_allocation (prog: tag aprogram) : tag aprogram * arg name_envt name_envt =
  let rec help_aexpr (body : tag aexpr) (si : int) (env : arg name_envt) : arg name_envt * int =
    match body with
    | ASeq(cexp, aexp, _) ->
        let (lhs_env, lhs_si) = help_cexpr cexp si env in
        help_aexpr aexp lhs_si lhs_env
    | ALet(sym, bind, body, _) ->
        let newenv = (sym, RegOffset(~-si*word_size, RBP)) :: env in
        let (bindenv, newsi) = help_cexpr bind (si+1) newenv in
        help_aexpr body newsi bindenv
    | ALetRec(bindings, body, _) ->
      let (bindings_env, bindings_si) =
        List.fold_left (fun (accum_env, accum_si) (name, _) ->
          ((name, RegOffset(~-accum_si*word_size, RBP))::accum_env, accum_si + 1))
        (env, si)
        bindings in
      let (new_env, new_si) =
        List.fold_left (fun (accum_env, accum_si) (_, exp) ->
          help_cexpr exp accum_si accum_env)
        (bindings_env, bindings_si)
        bindings in
      help_aexpr body new_si new_env
    | ACExpr(cexpr) -> help_cexpr cexpr si env
  and help_cexpr (expr : tag cexpr) (si : int) (env : arg name_envt) : arg name_envt * int =
    match expr with
    | CIf(cond, lhs, rhs, _) ->
        let (lhs_env, lhs_si) = help_aexpr lhs si env in
        help_aexpr rhs lhs_si lhs_env
    | CScIf(cond, lhs, rhs, _) ->
        let (lhs_env, lhs_si) = help_aexpr lhs si env in
        help_aexpr rhs lhs_si lhs_env
    | CPrim1 _ -> (env, si)
    | CPrim2 _ -> (env, si)
    | CApp _ -> (env, si)
    | CImmExpr _ -> (env, si)
    | CTuple _ -> (env, si)
    | CGetItem _ -> (env, si)
    | CSetItem _ -> (env, si)
    | CLambda(args, body, tag) ->
        let args_with_idx = List.mapi (fun i arg -> (arg, RegOffset((i + 3)*word_size, RBP))) args in
        let new_env = List.fold_left (fun accum_env cell -> cell :: accum_env) env args_with_idx in
        let self_name = sprintf "closure$%d" tag in
        let new_env_with_self = (self_name, RegOffset(2*word_size, RBP)) :: new_env in
        let (env_with_body_slots, _) = help_aexpr body 1 new_env_with_self in
        (env_with_body_slots, si)
  in
  match prog with
  | AProgram(body, _) ->
      let (prog_env, _) = help_aexpr body 1 [] in
      (prog, ["dummy_name_envt", prog_env])
