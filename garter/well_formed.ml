(* open Printf
open Pretty *)
open Phases
open Exprs
(* open Assembly *)
open Errors
open Util

let native_fun_bindings = [];;

(* you can add any functions or data defined by the runtime here for future use *)
let initial_val_env = []

let initial_fun_env = prim_bindings @ native_fun_bindings

let env_keys e = List.map fst e
                            
(* Prepends a list-like env onto an name_envt *)
let merge_envs list_env1 list_env2 =
  list_env1 @ list_env2

(* Scope_info stores the location where something was defined,
   and if it was a function declaration, then its type arity and argument arity *)
type scope_info = (sourcespan * int option * int option)
let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  let rec wf_E e (env : scope_info name_envt) =
    debug_printf "In wf_E: %s\n" (ExtString.String.join ", " (env_keys env));
    match e with
    | ESeq(e1, e2, _) -> wf_E e1 env @ wf_E e2 env
    | ETuple(es, _) -> List.concat (List.map (fun e -> wf_E e env) es)
    | EGetItem(e, idx, pos) ->
       wf_E e env @ wf_E idx env
    | ESetItem(e, idx, newval, pos) ->
       wf_E e env @ wf_E idx env @ wf_E newval env
    | ENil _ -> []
    | EBool _ -> []
    | ENumber(n, loc) ->
       if n > (Int64.div Int64.max_int 2L) || n < (Int64.div Int64.min_int 2L) then
         [Overflow(n, loc)]
       else
         []
    | EId (x, loc) -> if (find_one (List.map fst env) x) then [] else [UnboundId(x, loc)]
    | EPrim1(_, e, _) -> wf_E e env
    | EPrim2(_, l, r, _) -> wf_E l env @ wf_E r env
    | EIf(c, t, f, _) -> wf_E c env @ wf_E t env @ wf_E f env
    | ELet(bindings, body, _) ->
       let rec find_locs x (binds : 'a bind list) : 'a list =
         match binds with
         | [] -> []
         | BBlank _::rest -> find_locs x rest
         | BName(y, _, loc)::rest ->
            if x = y then loc :: find_locs x rest
            else  find_locs x rest
         | BTuple(binds, _)::rest -> find_locs x binds @ find_locs x rest in
       let rec find_dupes (binds : 'a bind list) : exn list =
         match binds with
         | [] -> []
         | (BBlank _::rest) -> find_dupes rest
         | (BName(x, _, def)::rest) -> (List.map (fun use -> DuplicateId(x, use, def)) (find_locs x rest)) @ (find_dupes rest)
         | (BTuple(binds, _)::rest) -> find_dupes (binds @ rest) in
       let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) bindings) in
       let rec process_binds (rem_binds : 'a bind list) (env : scope_info name_envt) =
         match rem_binds with
         | [] -> (env, [])
         | BBlank _::rest -> process_binds rest env
         | BTuple(binds, _)::rest -> process_binds (binds @ rest) env
         | BName(x, allow_shadow, xloc)::rest ->
            let shadow =
              if allow_shadow then []
              else match find_opt env x with
                   | None -> []
                   | Some (existing, _, _) -> [ShadowId(x, xloc, existing)] in
            let new_env = (x, (xloc, None, None))::env in
            let (newer_env, errs) = process_binds rest new_env in
            (newer_env, (shadow @ errs)) in
       let rec process_bindings bindings (env : scope_info name_envt) =
         match bindings with
         | [] -> (env, [])
         | (b, e, loc)::rest ->
            let errs_e = wf_E e env in
            let (env', errs) = process_binds [b] env in
            let (env'', errs') = process_bindings rest env' in
            (env'', errs @ errs_e @ errs') in
       let (env2, errs) = process_bindings bindings env in
       dupeIds @ errs @ wf_E body env2
    | EApp(func, args, native, loc) ->
       let rec_errors = List.concat (List.map (fun e -> wf_E e env) (func :: args)) in
       (match func with
        | EId(funname, _) -> 
           (match (find_opt env funname) with
            | Some(_, _, Some arg_arity) ->
               let actual = List.length args in
               if actual != arg_arity then [Arity(arg_arity, actual, loc)] else []
            | _ -> [])
        | _ -> [])
       @ rec_errors
    | ELetRec(binds, body, _) ->
       let nonfuns = List.find_all (fun b -> match b with | (BName _, ELambda _, _) -> false | _ -> true) binds in
       let nonfun_errs = List.map (fun (b, _, where) -> LetRecNonFunction(b, where)) nonfuns in

     
       let rec find_locs x (binds : 'a bind list) : 'a list =
         match binds with
         | [] -> []
         | BBlank _::rest -> find_locs x rest
         | BName(y, _, loc)::rest ->
            if x = y then loc :: find_locs x rest
            else  find_locs x rest
         | BTuple(binds, _)::rest -> find_locs x binds @ find_locs x rest in
       let rec find_dupes (binds : 'a bind list) : exn list =
         match binds with
         | [] -> []
         | (BBlank _::rest) -> find_dupes rest
         | (BName(x, _, def)::rest) -> List.map (fun use -> DuplicateId(x, use, def)) (find_locs x rest)
         | (BTuple(binds, _)::rest) -> find_dupes (binds @ rest) in
       let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) binds) in
       let rec process_binds (rem_binds : sourcespan bind list) (env : scope_info name_envt) =
         match rem_binds with
         | [] -> (env, [])
         | BBlank _::rest -> process_binds rest env
         | BTuple(binds, _)::rest -> process_binds (binds @ rest) env
         | BName(x, allow_shadow, xloc)::rest ->
            let shadow =
              if allow_shadow then []
              else match (find_opt env x) with
                   | None -> []
                   | Some (existing, _, _) -> if xloc = existing then [] else [ShadowId(x, xloc, existing)] in
            let new_env = (x, (xloc, None, None))::env in
            let (newer_env, errs) = process_binds rest new_env in
            (newer_env, (shadow @ errs)) in

       let (env, bind_errs) = process_binds (List.map (fun (b, _, _) -> b) binds) env in
       
       let rec process_bindings bindings env =
         match bindings with
         | [] -> (env, [])
         | (b, e, loc)::rest ->
            let (env, errs) = process_binds [b] env in
            let errs_e = wf_E e env in
            let (env', errs') = process_bindings rest env in
            (env', errs @ errs_e @ errs') in
       let (new_env, binding_errs) = process_bindings binds env in

       let rhs_problems = List.map (fun (_, rhs, _) -> wf_E rhs new_env) binds in
       let body_problems = wf_E body new_env in
       nonfun_errs @ dupeIds @ bind_errs @ binding_errs @ (List.flatten rhs_problems) @ body_problems
    | ELambda(binds, body, _) ->
       let rec dupe x args =
         match args with
         | [] -> None
         | BName(y, _, loc)::_ when x = y -> Some loc
         | BTuple(binds, _)::rest -> dupe x (binds @ rest)
         | _::rest -> dupe x rest in
       let rec process_args rem_args =
         match rem_args with
         | [] -> []
         | BBlank _::rest -> process_args rest
         | BName(x, _, loc)::rest ->
            (match dupe x rest with
             | None -> []
             | Some where -> [DuplicateId(x, where, loc)]) @ process_args rest
         | BTuple(binds, loc)::rest ->
            process_args (binds @ rest)
       in
       let rec flatten_bind (bind : sourcespan bind) : (string * scope_info) list =
         match bind with
         | BBlank _ -> []
         | BName(x, _, xloc) -> [(x, (xloc, None, None))]
         | BTuple(args, _) -> List.concat (List.map flatten_bind args) in
       (process_args binds) @ wf_E body (merge_envs (List.concat (List.map flatten_bind binds)) env)
  and wf_D d (env : scope_info name_envt) (tyenv : StringSet.t) =
    match d with
    | DFun(_, args, body, _) ->
       let rec dupe x args =
         match args with
         | [] -> None
         | BName(y, _, loc)::_ when x = y -> Some loc
         | BTuple(binds, _)::rest -> dupe x (binds @ rest)
         | _::rest -> dupe x rest in
       let rec process_args rem_args =
         match rem_args with
         | [] -> []
         | BBlank _::rest -> process_args rest
         | BName(x, _, loc)::rest ->
            (match dupe x rest with
             | None -> []
             | Some where -> [DuplicateId(x, where, loc)]) @ process_args rest
         | BTuple(binds, loc)::rest ->
            process_args (binds @ rest)
       in
       let rec arg_env args (env : scope_info name_envt) =
         match args with
         | [] -> env
         | BBlank _ :: rest -> arg_env rest env
         | BName(name, _, loc)::rest -> (name, (loc, None, None))::(arg_env rest env)
         | BTuple(binds, _)::rest -> arg_env (binds @ rest) env in
       (process_args args) @ (wf_E body (arg_env args env))
  and wf_G (g : sourcespan decl list) (env : scope_info name_envt) (tyenv : StringSet.t) =
    let add_funbind (env : scope_info name_envt) d =
      match d with
      | DFun(name, args, _, loc) ->
         (name, (loc, Some (List.length args), Some (List.length args)))::env in
    let env = List.fold_left add_funbind env g in
    let errs = List.concat (List.map (fun d -> wf_D d env tyenv) g) in
    (errs, env)
  in
  match p with
  | Program(decls, body, _) ->
     let initial_env = initial_val_env in
     let initial_env = List.fold_left
                          (fun env (name, (_, arg_count)) -> (name, (dummy_span, Some arg_count, Some arg_count))::env)
     initial_fun_env
     initial_env in
     let rec find name (decls : 'a decl list) =
       match decls with
       | [] -> None
       | DFun(n, args, _, loc)::rest when n = name -> Some(loc)
       | _::rest -> find name rest in
     let rec dupe_funbinds decls =
       match decls with
       | [] -> []
       | DFun(name, args, _, loc)::rest ->
          (match find name rest with
          | None -> []
          | Some where -> [DuplicateFun(name, where, loc)]) @ dupe_funbinds rest in
     let all_decls = List.flatten decls in
     let initial_tyenv = StringSet.of_list ["Int"; "Bool"] in
     let help_G (env, exns) g =
       let (g_exns, funbinds) = wf_G g env initial_tyenv in
       (List.fold_left (fun xs x -> x::xs) env funbinds, exns @ g_exns) in
     let (env, exns) = List.fold_left help_G (initial_env, dupe_funbinds all_decls) decls in
     debug_printf "In wf_P: %s\n" (ExtString.String.join ", " (env_keys env));
     let exns = exns @ (wf_E body env)
     in match exns with
        | [] -> Ok p
        | _ -> Error exns

(* (* Our envs track existence+location of either a var (let binding) or function with arity *)
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
  let rec add_group_to_env_check_errs (decgrp : sourcespan decl list) (env : env_entry envt) : (env_entry envt * exn list) =
  let (env_with_group, dup_exns) = List.fold_left (
    fun (env_acc, errs_acc) decl ->
      match decl with
      | DFun(name, _, _, loc) ->
        let dup_exns =
          begin
          match (maybe_loc_from_env name env_acc) with
          | None -> []
          | Some(existing_loc) -> [DuplicateFun(name, loc, existing_loc)]
          end in
        ((name, Id(loc)) :: env_acc, dup_exns @ errs_acc)
    )
    (env, [])
    decgrp in
  let fbody_exns = wf_DGroup decgrp env_with_group in
  (env_with_group, fbody_exns @ dup_exns)
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
      | EApp(func, args, _, loc) ->
        let func_errs = wf_E func env in
        let arg_errs = List.fold_left (fun errs arg -> errs @ (wf_E arg env)) [] args in
        func_errs @ arg_errs
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
        Error(all_errs) *)
