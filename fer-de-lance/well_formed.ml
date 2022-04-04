(* open Printf
open Pretty *)
open Phases
open Exprs
(* open Assembly *)
open Errors
open Util

(* Our envs track existence+location of either a var (let binding) or function with arity *)
type env_entry =
  | Id of sourcespan

(* Given a function name and a list of decls, this function will check whether the function name
 * is duplicated in the decl list. If it is, then we will return a list that contains the
 * DuplicateFun error. Also takes in location where the function was just declared. *)
let rec check_duplicate_decl (fname : string) (decls : sourcespan decl list) (loc : sourcespan) : exn list =
  match (find_decl decls fname) with
  | None -> []  (* no duplicates found -> no error *)
  | Some(DFun(_, _, _, existing_loc)) -> [DuplicateFun(fname, existing_loc, loc)]

(* checks for duplicate variables inside a let binding.  we do this by looking through a flattened list of (string * sourcepan) to make our lives easier. *)
let rec check_duplicate_binds (sym : string) (existing_loc : sourcespan) (binds : (string * sourcespan) list) : exn list =
  match binds with
  | [] -> [] (* no duplicates found -> no error *)
  | (k, loc) :: tail ->
      if k = sym then
        [DuplicateId(sym, loc, existing_loc)]
      else
        check_duplicate_binds sym loc tail

let rec check_duplicate_arg (sym : string) (args : (string * sourcespan) list) (loc : sourcespan) : exn list =
  match args with
  | [] -> [] (* no duplicates found -> no error *)
  | (k, existing_loc) :: tail ->
      if k = sym then
        [DuplicateId(sym, existing_loc, loc)]
      else
        check_duplicate_arg sym tail loc

(* Is the id in the env? *)
let rec id_in_env (id : string) (env : env_entry envt) : bool =
  match env with
  | [] -> false
  | (k, Id(_)) :: tail ->
      if id = k then true
      else id_in_env id tail

(* Get Some(loc) if id is in the env, else None *)
let rec maybe_loc_from_env (id : string) (env : env_entry envt) : sourcespan option =
  match env with
  | [] -> None
  | (k, Id(loc)) :: tail ->
      if id = k then Some(loc)
      else maybe_loc_from_env id tail

(* Add a list of unique args to an env as Vars *)
let rec add_args_to_env (args : (string * sourcespan) list) (env : env_entry envt) : env_entry envt =
  (* fold direction doesn't matter since arg names are required to be unique *)
  List.fold_left
    (fun env_acc arg ->
      match arg with
      | (arg_name, loc) -> (arg_name, Id(loc)) :: env_acc)
    env
    args

let rec bind_pairs (binds : sourcespan bind list) : (string * sourcespan) list =
  match binds with
  | [] -> []
  | BBlank(loc) :: tail -> bind_pairs tail
  | BName(sym,_,loc) :: tail -> (sym,loc) :: (bind_pairs tail)
  | BTuple(tup_binds,loc) :: tail -> (bind_pairs tup_binds) @ (bind_pairs tail)

let rec bind_list_pairs (binds : sourcespan binding list) : (string * sourcespan) list =
  match binds with
  | [] -> []
  | (bind,_,_) :: tail -> (bind_pairs [bind]) @ (bind_list_pairs tail)

let rec check_dups (binds : (string * sourcespan) list) : exn list =
  match binds with
  | [] -> []
  | (sym,loc) :: tail -> (check_duplicate_binds sym loc tail) @ (check_dups tail)

let dup_binding_exns (binds : sourcespan binding list) : exn list =
  check_dups (bind_list_pairs binds)

let dup_bind_exns (binds : sourcespan bind list) : exn list =
  check_dups (bind_pairs binds)

let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  (* Goes through the list of function decls and adds them all to our env.  We also
   * gather any errors along the way. *)
  let rec setup_env (d : sourcespan decl list) (init_env : env_entry envt) : (env_entry envt) * (exn list) =
    match d with
    | [] -> (init_env, [])
    | DFun(fname, args, body, loc) :: tail ->
        let (tail_env, tail_errs) = (setup_env tail init_env) in
        let new_errs = (check_duplicate_decl fname tail loc) @ tail_errs in
        let new_env = (fname, Id(loc)) :: tail_env in
        (new_env, new_errs)
  and add_group_to_env_check_errs (decgrp : sourcespan decl list) (env : env_entry envt) : (env_entry envt * exn list) =
  List.fold_left (
    fun (env_acc, errs_acc) decl ->
      match decl with
      | DFun(name, _, _, loc) ->
        let dup_exns = 
          begin
          match (maybe_loc_from_env name env_acc) with
          | None -> []
          | Some(existing_loc) -> [DuplicateFun(name, loc, existing_loc)]
          end in
        let fbody_exns = wf_D decl env_acc in
        ((name, Id(loc)) :: env_acc, fbody_exns @ dup_exns @ errs_acc))
    (env, [])
    decgrp
  (* checks an expr to see if it's well formed *)
  and wf_E (e : sourcespan expr) (env : env_entry envt) : (exn list) =
    match e with
      | ESeq(frst, scnd, _) -> (wf_E frst env) @ (wf_E scnd env)
      | ETuple(elems, _) ->
        List.fold_left (fun errs elem -> errs @ (wf_E elem env)) [] elems
      | EGetItem(tup, idx, _) -> (wf_E tup env) @ (wf_E idx env)
      | ESetItem(tup, idx, nval, _) -> (wf_E tup env) @ (wf_E idx env) @ (wf_E nval env)
      | ELet(binds, body, _) ->
        let dup_exns = dup_binding_exns binds in
        let (let_env, let_errs) = wf_Bindings binds env in
        dup_exns @ let_errs @ (wf_E body let_env)
      | EPrim1(op, expr, _) -> wf_E expr env
      | EPrim2(op, lhs, rhs, _) -> (wf_E lhs env) @ (wf_E rhs env)
      | EIf(cond, thn, els, _) -> (wf_E cond env) @ (wf_E thn env) @ (wf_E els env)
      | EScIf(cond, thn, els, _) -> raise (InternalCompilerError "EScIf is not in the egg-eater syntax")
      | ENumber(n, loc) ->
          if n > (Int64.div Int64.max_int 2L) || n < (Int64.div Int64.min_int 2L) then
            [Overflow(n, loc)]
          else
            []
      | EBool _ -> []
      | ENil _ -> []
      | EId(id, loc) ->
          if id_in_env id env then []
          else [UnboundId(id, loc)]
      | EApp(fname, args, _, loc) ->
        let arg_errs = List.fold_left (fun errs arg -> errs @ (wf_E arg env)) [] args in
        arg_errs
      | ELambda(args, body, loc) ->
        let args_extracted = bind_pairs args in
        let args_errs = check_dups args_extracted in
        let new_env = add_args_to_env args_extracted env in
        let body_errs = wf_E body new_env in
        args_errs @ body_errs
      | ELetRec(bindings, body, loc) ->
        let bindings_extracted = (bind_list_pairs bindings) in
        let bindings_dups = check_dups bindings_extracted in
        let new_env = add_args_to_env bindings_extracted env in
        let bindings_errs = List.fold_left
                            (fun errs_acc (_, bind_body, _) -> (wf_E bind_body new_env) @ errs_acc)
                            []
                            bindings in
        let body_errs = (wf_E body new_env) in
        bindings_dups @ bindings_errs @ body_errs
  and wf_D (d : sourcespan decl) (env : env_entry envt) : exn list =
    match d with
    | DFun(fname, args, body, _) ->
        let flattened_args = bind_pairs args in
        let new_env = add_args_to_env flattened_args env
        in (check_dups flattened_args) @ (wf_E body new_env)
  and wf_Bindings (bindings : sourcespan binding list) (env : env_entry envt) : (env_entry envt) * (exn list) =
    match bindings with
    | [] -> (env, [])
    | (bind,expr,_)::tail ->
        let (env_bind, exns_bind) = wf_Bind bind env in
        let exns_expr = wf_E expr env in
        let (env_tail, exns_tail) = wf_Bindings tail env_bind in
        (env_tail, exns_bind @ exns_expr @ exns_tail)
  and wf_Bind (bnd : sourcespan bind) (env : env_entry envt) : (env_entry envt) * (exn list) =
    match bnd with
    | BBlank(_) -> (env, [])
    | BName(name, _, loc) -> ((name, Id(loc))::env, [])
    | BTuple(binds, _) ->
      List.fold_left
      (fun (acc : (env_entry envt) * (exn list)) bnd ->
        let (env_acc, exns_acc) = acc in
        let (benv, bexns) = (wf_Bind bnd env_acc) in (benv, bexns @ exns_acc))
      (env, [])
      binds
  and wf_DGroup (group : sourcespan decl list) (env : env_entry envt) : exn list =
    match group with
    | [] -> []
    | decl :: rest ->
      let decl_exns = wf_D decl env in
      decl_exns @ (wf_DGroup rest env)
  in
  match p with
  | Program(decls, body, fake_loc) ->
      let init_env = [("cinput",Id(fake_loc)); ("cequal",Id(fake_loc))] in
      (* check decls *)
      let (decls_env, decl_errs) =
        List.fold_left
          (fun ((env_acc, exns_acc) : (env_entry envt * exn list)) decgrp ->
            let (new_env, new_exns) = add_group_to_env_check_errs decgrp env_acc in
            (new_env, new_exns @ exns_acc))
          (init_env, [])
          decls in
      (* check the body *)
      let body_errs = wf_E body decls_env in
      let all_errs = decl_errs @ body_errs in
      if all_errs = [] then
        Ok(p)
      else
        Error(all_errs)
