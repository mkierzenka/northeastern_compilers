open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
       
type 'a envt = (string * 'a) list

(* Our envs track existence+location of either a var (let binding) or function with arity *)
type env_entry =
  | Var of sourcespan
  | Func of int * sourcespan
;;


(* This is unused (should fix before ever using it, e.g. support Tuples)
let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1(_, e, _) -> is_imm e
  | EPrim2(_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet(binds, body, _) ->
     List.for_all (fun (_, e, _) -> is_anf e) binds
     && is_anf body
  | EIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | _ -> is_imm e
and is_imm e =
  match e with
  | ENumber _ -> true
  | EBool _ -> true
  | EId _ -> true
  | _ -> false
;;*)


let const_true     = HexConst(0xFFFFFFFFFFFFFFFFL)
let const_false    = HexConst(0x7FFFFFFFFFFFFFFFL)
let bool_mask      = HexConst(0x8000000000000000L)
let bool_tag       = 0x0000000000000007L
let bool_tag_mask  = 0x0000000000000007L
let num_tag        = 0x0000000000000000L
let num_tag_mask   = 0x0000000000000001L

let err_COMP_NOT_NUM   = 1L
let err_ARITH_NOT_NUM  = 2L
let err_LOGIC_NOT_BOOL = 3L
let err_IF_NOT_BOOL    = 4L
let err_OVERFLOW       = 5L
let err_GET_NOT_TUPLE  = 6L
let err_GET_LOW_INDEX  = 7L
let err_GET_HIGH_INDEX = 8L
let err_NIL_DEREF      = 9L

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]
let heap_reg = R15
let scratch_reg = R11


(* You may find some of these helpers useful *)
let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y,v)::rest ->
     if y = x then v else find rest x
let rec find_opt ls x =
  match ls with
  | [] -> None
  | (y,v)::rest ->
     if y = x then Some v else find_opt rest x

let count_vars e =
  let rec helpA e =
    match e with
    | ALet(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf(_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in helpA e

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))


let rec find_decl (ds : 'a decl list) (name : string) : 'a decl option =
  match ds with
    | [] -> None
    | (DFun(fname, _, _, _) as d)::ds_rest ->
      if name = fname then Some(d) else find_decl ds_rest name

let rec find_one (l : 'a list) (elt : 'a) : bool =
  match l with
    | [] -> false
    | x::xs -> (elt = x) || (find_one xs elt)

let rec find_dup (l : 'a list) : 'a option =
  match l with
    | [] -> None
    | [x] -> None
    | x::xs ->
      if find_one xs x then Some(x) else find_dup xs
;;

type funenvt = call_type envt;;
let initial_fun_env : funenvt = [
  (* call_types indicate whether a given function is implemented by something in the runtime,
     as a snake function, as a primop (in case that's useful), or just unknown so far *)
];;


let rename_and_tag (p : tag program) : tag program =
  let rec rename (env : string envt) p =
    match p with
    | Program(decls, body, tag) ->
       let rec addToEnv funenv decl =
         match decl with
         | DFun(name, _, _, _) -> (name, Snake)::funenv in
       let initial_funenv = List.map (fun (name, ct) -> (name, ct)) initial_fun_env in
       let funenv = List.fold_left addToEnv initial_funenv decls in
       Program(List.map (helpD funenv env) decls, helpE funenv env body, tag)
  and helpD funenv env decl =
    match decl with
    | DFun(name, args, body, tag) ->
       let (newArgs, env') = helpBS env args in
       DFun(name, newArgs, helpE funenv env' body, tag)
  and helpB env b =
    match b with
    | BBlank tag -> (b, env)
    | BName(name, allow_shadow, tag) ->
       let name' = sprintf "%s_%d" name tag in
       (BName(name', allow_shadow, tag), (name, name') :: env)
    | BTuple(binds, tag) ->
       let (binds', env') = helpBS env binds in
       (BTuple(binds', tag), env')
  and helpBS env (bs : tag bind list) =
    match bs with
    | [] -> ([], env)
    | b::bs ->
       let (b', env') = helpB env b in
       let (bs', env'') = helpBS env' bs in
       (b'::bs', env'')
  and helpBG funenv env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a)::bindings ->
       let (b', env') = helpB env b in
       let e' = helpE funenv env e in
       let (bindings', env'') = helpBG funenv env' bindings in
       ((b', e', a)::bindings', env'')
  and helpE funenv env e =
    match e with
    | ESeq(e1, e2, tag) -> ESeq(helpE funenv env e1, helpE funenv env e2, tag)
    | ETuple(es, tag) -> ETuple(List.map (helpE funenv env) es, tag)
    | EGetItem(e, idx, tag) -> EGetItem(helpE funenv env e, helpE funenv env idx, tag)
    | ESetItem(e, idx, newval, tag) -> ESetItem(helpE funenv env e, helpE funenv env idx, helpE funenv env newval, tag)
    | EPrim1(op, arg, tag) -> EPrim1(op, helpE funenv env arg, tag)
    | EPrim2(op, left, right, tag) -> EPrim2(op, helpE funenv env left, helpE funenv env right, tag)
    | EIf(c, t, f, tag) -> EIf(helpE funenv env c, helpE funenv env t, helpE funenv env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId(name, tag) ->
       (try
         EId(find env name, tag)
       with Not_found -> e)
    | EApp(name, args, native, tag) ->
       let call_type = match find_opt funenv name with None -> native | Some ct -> ct in
       EApp(name, List.map (helpE funenv env) args, call_type, tag)
    | ELet(binds, body, tag) ->
       let (binds', env') = helpBG funenv env binds in
       let body' = helpE funenv env' body in
       ELet(binds', body', tag)
  in (rename [] p)
;;

(* Returns the stack-index (in words) of the deepest stack index used for any 
   of the variables in this expression *)
let deepest_stack e env =
  let rec helpA e =
    match e with
    | ALet(name, bind, body, _) -> List.fold_left max 0 [name_to_offset name; helpC bind; helpA body]
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf(c, t, f, _) -> List.fold_left max 0 [helpI c; helpA t; helpA f]
    | CPrim1(_, i, _) -> helpI i
    | CPrim2(_, i1, i2, _) -> max (helpI i1) (helpI i2)
    | CApp(_, args, _, _) -> List.fold_left max 0 (List.map helpI args)
    | CTuple(elms, _) -> List.fold_left max 0 (List.map helpI elms)
    | CGetItem(tup, idx, _) -> max (helpI tup) (helpI idx)
    | CSetItem(tup, idx, newval, _) -> List.fold_left max 0 [helpI tup; helpI idx; helpI newval]
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmNil _ -> 0
    | ImmId(name, _) -> name_to_offset name
  and name_to_offset name =
    match (find env name) with
    | RegOffset(bytes, RBP) -> bytes / (-1 * word_size)  (* negative because stack direction *)
    | _ -> 0
  in max (helpA e) 0 (* if only parameters are used, helpA might return a negative value *)
;;


(* IMPLEMENT EVERYTHING BELOW *)


let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program(decls, body, _) -> AProgram(List.map helpD decls, helpA body, ())
  and helpD (d : tag decl) : unit adecl =
    match d with
    | DFun(name, args, body, _) ->
       let args = List.map
         (fun a ->
           match a with
           | BBlank(tag) -> "blank" (* TODO is this necessary? *)
           | BName(a, _, _) -> a
           | BTuple(bindl, _) -> raise (InternalCompilerError "desugaring failed: tuples cannot be ANFed in function decl args"))
         args in
       ADFun(name, args, helpA body, ())
  and helpC (e : tag expr) : (unit cexpr * (string * unit cexpr) list) = 
    match e with
    | EPrim1(op, arg, _) ->
       let (arg_imm, arg_setup) = helpI arg in
       (CPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, left, right, _) ->
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (CPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
       let (cond_imm, cond_setup) = helpI cond in
       (CIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ELet([], body, _) -> helpC body
    | ELet((bind, expr, tag)::tail, body, _) ->
       (* TODO make sure using same tag for all bindings is ok *)
       let (expr_ans, expr_setup) = helpC expr in
       let (body_ans, body_setup) = helpC (ELet(tail, body, tag)) in
       begin match bind with
       | BBlank(_) ->
           let dummy_bind = "blank" in (* TODO better name? *)
           (body_ans, expr_setup @ [(dummy_bind, expr_ans)] @ body_setup)
       | BName(sym, _, _) ->
           (body_ans, expr_setup @ [(sym, expr_ans)] @ body_setup)
       | BTuple _ -> raise (InternalCompilerError "desugaring failed: tuples cannot be ANFed in let bindings")
       end
    | EApp(funname, args, ct, _) ->
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (CApp(funname, new_args, ct, ()), List.concat new_setup)
    (* NOTE: You may need more cases here, for sequences and tuples *)
    | ESeq _ -> raise (InternalCompilerError "desugaring failed: sequences cannot be ANFed")
    | ETuple([], tag) -> (CTuple([], ()), []) (* TODO is this nil? *)
    | ETuple(elem::tail, tag) ->
       let (elem_ans, elem_setup) = helpI elem in
       let (tail_ans, tail_setup) = helpC (ETuple(tail, tag)) in
       begin match tail_ans with
       | CTuple(tail_elems, _) ->
           (CTuple(elem_ans::tail_elems, ()), elem_setup @ tail_setup)
       | _ -> raise (InternalCompilerError "error ANFing tuples")
       end
    | EGetItem(tup, idx, _) ->
        let (tup_ans, tup_env) = helpI tup in
        let (idx_ans, idx_env) = helpI idx in
        (CGetItem(tup_ans, idx_ans, ()), tup_env @ idx_env)
    | ESetItem(tup, idx, nval, _) ->
        let (tup_ans, tup_env) = helpI tup in
        let (idx_ans, idx_env) = helpI idx in
        let (nval_ans, nval_env) = helpI nval in
        (CSetItem(tup_ans, idx_ans, nval_ans, ()), tup_env @ idx_env @ nval_env)
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * (string * unit cexpr) list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])
    | ENil(_) -> (ImmNil(()), [])
    | EPrim1(op, arg, tag) ->
       let tmp = sprintf "unary_%d" tag in
       let (arg_imm, arg_setup) = helpI arg in
       (ImmId(tmp, ()), arg_setup @ [(tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
       let tmp = sprintf "binop_%d" tag in
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (ImmId(tmp, ()), left_setup @ right_setup @ [(tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [(tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(funname, args, ct, tag) ->
       let tmp = sprintf "app_%d" tag in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), (List.concat new_setup) @ [(tmp, CApp(funname, new_args, ct, ()))])
    | ELet([], body, _) -> helpI body
    | ELet(_::_, body, tag) ->
       let tmp = sprintf "let_%d" tag in
       let (let_ans, let_setup) = helpC e in
       (ImmId(tmp, ()), let_setup @ [(tmp, let_ans)])
    | ESeq _ -> raise (InternalCompilerError "desugaring failed: sequences cannot be ANFed")
    | ETuple(_, tag) ->
       let tmp = sprintf "tuple_%d" tag in
       let (tup_ans, tup_setup) = helpC e in
       (ImmId(tmp, ()), tup_setup @ [(tmp, tup_ans)])
    | EGetItem(_, _, tag) ->
       let tmp = sprintf "getitem_%d" tag in
       let (gi_ans, gi_setup) = helpC e in
       (ImmId(tmp, ()), gi_setup @ [(tmp, gi_ans)])
    | ESetItem(_, _, _, tag) ->
       let tmp = sprintf "setitem_%d" tag in
       let (si_ans, si_setup) = helpC e in
       (ImmId(tmp, ()), si_setup @ [(tmp, si_ans)])

  and helpA e : unit aexpr = 
    let (ans, ans_setup) = helpC e in
    List.fold_right (fun (bind, exp) body -> ALet(bind, exp, body, ())) ans_setup (ACExpr ans)
  in
  helpP p
;;

(* Given a function name and a list of decls, this function will check whether the function name
 * is duplicated in the decl list. If it is, then we will return a list that contains the
 * DuplicateFun error. Also takes in location where the function was just declared. *)
let rec check_duplicate_decl (fname : string) (decls : sourcespan decl list) (loc : sourcespan) : exn list =
  match (find_decl decls fname) with
  | None -> []  (* no duplicates found -> no error *)
  | Some(DFun(_, _, _, existing_loc)) -> [DuplicateFun(fname, existing_loc, loc)]
;;

(* Checks if a sym is already bound in a binds list, returns an exception if so otherwise empty list. Also takes in location where this symbol was just bound. *)
(*
let rec check_duplicate_var (sym : string) (binds : sourcespan binding list) (loc : sourcespan) : exn list =
  match binds with
  | [] -> [] (* no duplicates found -> no error *)
  | (k, v, existing_loc) :: tail ->
      if k = sym then
        [DuplicateId(sym, existing_loc, loc)]
      else
        check_duplicate_var sym tail loc
;;
*)

(* checks for duplicate variables inside a let binding.  we do this by looking through a flattened list of (string * sourcepan) to make our lives easier. *)
let rec check_duplicate_binds (sym : string) (existing_loc : sourcespan) (binds : (string * sourcespan) list) : exn list =
  match binds with
  | [] -> [] (* no duplicates found -> no error *)
  | (k, loc) :: tail ->
      if k = sym then
        [DuplicateId(sym, loc, existing_loc)]
      else
        check_duplicate_binds sym loc tail
;;

let rec check_duplicate_arg (sym : string) (args : (string * sourcespan) list) (loc : sourcespan) : exn list =
  match args with
  | [] -> [] (* no duplicates found -> no error *)
  | (k, existing_loc) :: tail ->
      if k = sym then
        [DuplicateId(sym, existing_loc, loc)]
      else
        check_duplicate_arg sym tail loc
;;

let rec var_in_env (id : string) (env : env_entry envt) : bool =
  match env with
  | [] -> false
  | (k, Var(_)) :: tail ->
      if id = k then true
      else var_in_env id tail
  | (k, Func(_)) :: tail ->
      (* an optimization: funcs are last in our env so by the time we see
       * the first func we know we can stop looking for a var *)
      false
;;

(* Lookup the loc of a variable in the env, will throw if not found *)
let rec lookup_var_loc (id : string) (env : env_entry envt) : sourcespan =
  match env with
  | [] -> raise (InternalCompilerError (sprintf "Var %s not found in env" id))
  | (k, Var(loc)) :: tail ->
      if id = k then loc
      else lookup_var_loc id tail
  | (k, Func(_)) :: tail ->
      (* an optimization: funcs are last in our env so by the time we see
       * the first func we know we can stop looking for a var *)
      raise (InternalCompilerError (sprintf "Var %s not found in env" id))
;;



let rec func_in_env (id : string) (env : env_entry envt) : bool =
  match env with
  | [] -> false
  | (k, Var(_)) :: tail ->
      (* this semantic choice stipulates that variables shadow functions *)
      if id = k then false
      else func_in_env id tail
  | (k, Func(_)) :: tail ->
      if id = k then true
      else func_in_env id tail
;;

(* Add a list of unique args to an env as Vars *)
let rec add_args_to_env (args : (string * sourcespan) list) (env : env_entry envt) : env_entry envt =
  (* fold direction doesn't matter since arg names are required to be unique *)
  List.fold_left
    (fun env_acc arg ->
      match arg with
      | (arg_name, loc) -> (arg_name, Var(loc)) :: env_acc)
    env
    args
;;

let rec bind_list_pairs (binds : sourcespan binding list) : (string * sourcespan) list =
  match binds with
  | [] -> []
  | (bind,_,_) :: tail -> (bind_pairs [bind]) @ (bind_list_pairs tail)
and bind_pairs (binds : sourcespan bind list) : (string * sourcespan) list =
  match binds with
  | [] -> []
  | BBlank(loc) :: tail -> bind_pairs tail
  | BName(sym,_,loc) :: tail -> (sym,loc) :: (bind_pairs tail)
  | BTuple(tup_binds,loc) :: tail -> (bind_pairs tup_binds) @ (bind_pairs tail)
;;

let rec check_dups (binds : (string * sourcespan) list) : exn list =
  match binds with
  | [] -> []
  | (sym,loc) :: tail -> (check_duplicate_binds sym loc tail) @ (check_dups tail)
;;

let dup_binding_exns (binds : sourcespan binding list) : exn list =
  check_dups (bind_list_pairs binds)
;;

(*
let dup_decl_args_exns (args : sourcespan bind list) : exn list =
  check_dups (bind_pairs args)
;;
*)


let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  (* Goes through the list of function decls and adds them all to our env.  We also
   * gather any errors along the way. *)
  let rec setup_env (d : sourcespan decl list) : (env_entry envt) * (exn list) =
    match d with
    | [] -> ([], [])
    | DFun(fname, args, body, loc) :: tail ->
        let (tail_env, tail_errs) = (setup_env tail) in
        let new_errs = (check_duplicate_decl fname tail loc) @ tail_errs in
        let new_env = (fname, Func(List.length args, loc)) :: tail_env in
        (new_env, new_errs)
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
      | ENumber(n, loc) ->
          if n > (Int64.div Int64.max_int 2L) || n < (Int64.div Int64.min_int 2L) then
            [Overflow(n, loc)]
          else
            []
      | EBool _ -> []
      | ENil _ -> []
      | EId(id, loc) ->
          if var_in_env id env then []
          else [UnboundId(id, loc)]
      | EApp(fname, args, _, loc) ->
        let arg_errs = List.fold_left (fun errs arg -> errs @ (wf_E arg env)) [] args in
        if func_in_env fname env then
          let id_t = find env fname in
          match id_t with
          | Func(arity, _) ->
              let callsite_arity = List.length args in
              if arity = callsite_arity then
                arg_errs
              else
                [Arity(arity, callsite_arity, loc)] @ arg_errs
          | Var(_) -> raise (InternalCompilerError (sprintf "Applying variable %s as a function" fname))
        else
          [UnboundFun(fname,loc)] @ arg_errs
  and wf_D (d : sourcespan decl) : exn list =
    match d with
    | DFun(fname, args, body, _) ->
        let flattened_args = bind_pairs args in
        let env = List.fold_left
          (fun accum_env arg_pair ->
            let (sym,loc) = arg_pair in
            (sym, Var(loc)) :: accum_env)
          [] flattened_args
        in (check_dups flattened_args) @ (wf_E body env)
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
    | BName(name, _, loc) -> ((name, Var(loc))::env, [])
    | BTuple(binds, _) ->
      List.fold_left
      (fun (acc : (env_entry envt) * (exn list)) bnd ->
        let (env_acc, exns_acc) = acc in
        let (benv, bexns) = (wf_Bind bnd env_acc) in (benv, bexns @ exns_acc))
      (env, [])
      binds
  in
  match p with
  | Program(decls, body, _) ->
      (* gather all functions into the env *)
      let (env, init_errs) = setup_env decls in
      (* check decls *)
      let decl_errs =
        List.fold_left
          (fun (acc : (exn list)) decl -> ((wf_D decl) @ acc))
          []
          decls in
      (* check the body *)
      let body_errs = wf_E body env in
      let all_errs = init_errs @ decl_errs @ body_errs in
      if all_errs = [] then
        Ok(p)
      else
        Error(all_errs)
;;

(* TODO, implement all our desugarings:
 - and/or rewrite
 - let bindings with tuple on the LHS
 - tuples as func args
 - add let binding for every func arg (to prevent tail-recursion overwrite)
 - sequence -> let bindings with "_"
*)
let desugar (p : sourcespan program) : sourcespan program =
  let gensym =
    let next = ref 0 in
    (fun name ->
      next := !next + 1;
      sprintf "%s_%d" name (!next)) in
  let rec helpE (e : sourcespan expr) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement desugaring for expressions"])
  and helpBinds (body : sourcespan expr) (bindlist : sourcespan bind list) (parent_sym : string) (parent_idx : int) : sourcespan expr =
    List.fold_left
      (fun body_acc arg ->
        match arg with
        | BBlank(_) -> body_acc
        | BName(sym, is_nested, bloc) ->
        if is_nested
        then ELet([(arg, EGetItem(EId(parent_sym), ENumber(parent_idx), bloc), bloc)], body_acc, loc) else ELet([(arg, EId(sym, bloc), bloc)], body_acc, loc)
        (* these locations aren't great, but nothing better it seems *)
        | BTuple(binds, bloc) -> ELet([(arg, EId(gensym, bloc), bloc)], body_acc, loc)
      )
      body
      bindlist
  and helpD (d : sourcespan decl) (* other parameters may be needed here *) =
    match d with
    | DFun(fname, args, body, loc) ->
        let desugared_body = List.fold_left
          (fun body_acc arg ->
            begin
            match arg with
            | BBlank(_) -> body_acc
            | BName(sym, _, bloc) -> ELet([(arg, EId(sym, bloc), bloc)], body_acc, loc) (* these locations aren't great, but nothing better it seems *)
            | BTuple(binds, bloc) -> helpBinds body_acc binds
            end
          )
          body
          args in
        DFun(fname, args, desugared_body, loc)
  in
  match p with
  | Program(decls, body, loc) ->
    let desugared_decls = List.map helpD decls in
    let desugared_body = helpE body in
    Program(desugared_decls, desugared_body, loc)
;;

let naive_stack_allocation (prog: tag aprogram) : tag aprogram * arg envt =
  raise (NotYetImplemented "Implement stack allocation for egg-eater")
;;


let rec compile_fun (fun_name : string) (args: string list) (env: arg envt) : instruction list =
  raise (NotYetImplemented "Compile funs not yet implemented")
and compile_aexpr (e : tag aexpr) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  raise (NotYetImplemented "Compile aexpr not yet implemented")
and compile_cexpr (e : tag cexpr) (env: arg envt) (num_args: int) (is_tail: bool) =
  raise (NotYetImplemented "Compile cexpr not yet implemented")
and compile_imm e env =
  match e with
  | ImmNum(n, _) -> Const(Int64.shift_left n 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)
  | ImmNil(_) -> raise (NotYetImplemented "Finish this")

let compile_decl (d : tag adecl) (env: arg envt) : instruction list =
  raise (NotYetImplemented "Compile decl not yet implemented")

let compile_prog ((anfed : tag aprogram), (env: arg envt)) : string =
  match anfed with
  | AProgram(decls, body, _) ->
     let comp_decls = raise (NotYetImplemented "... do stuff with decls ...") in
     let (body_prologue, comp_body, body_epilogue) = raise (NotYetImplemented "... do stuff with body ...") in
     
     let heap_start = [
         ILineComment("heap start");
         IInstrComment(IMov(Reg(heap_reg), Reg(List.nth first_six_args_registers 0)), "Load heap_reg with our argument, the heap pointer");
         IInstrComment(IAdd(Reg(heap_reg), Const(15L)), "Align it to the nearest multiple of 16");
         IInstrComment(IAnd(Reg(heap_reg), HexConst(0xFFFFFFFFFFFFFFF0L)), "by adding no more than 15 to it")
       ] in
     let main = to_asm (body_prologue @ heap_start @ comp_body @ body_epilogue) in
     
     raise (NotYetImplemented "... combine comp_decls and main with any needed extra setup and error handling ...")

(* Feel free to add additional phases to your pipeline.
   The final pipeline phase needs to return a string,
   but everything else is up to you. *)

;;

let run_if should_run f =
  if should_run then f else no_op_phase
;;

(* TODO, read assignment description-- we need comments here *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  (* TODO add desugaring, maybe not *right* here *)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename_and_tag)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase locate_bindings naive_stack_allocation)
  |> (add_phase result compile_prog)
;;
