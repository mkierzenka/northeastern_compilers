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
let const_nil      = HexConst(0x0000000000000001L)
let tup_tag        = 0x0000000000000001L
let tup_tag_mask   = 0x0000000000000007L

let err_COMP_NOT_NUM    = 1L
let err_ARITH_NOT_NUM   = 2L
let err_LOGIC_NOT_BOOL  = 3L
let err_IF_NOT_BOOL     = 4L
let err_OVERFLOW        = 5L
let err_GET_NOT_TUPLE   = 6L
let err_GET_LOW_INDEX   = 7L
let err_GET_HIGH_INDEX  = 8L
let err_NIL_DEREF       = 9L
let err_BAD_INPUT       = 10L
let err_TUP_IDX_NOT_NUM = 11L

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
    | EScIf(c, t, f, tag) -> EScIf(helpE funenv env c, helpE funenv env t, helpE funenv env f, tag)
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
    | CScIf(c, t, f, _) -> List.fold_left max 0 [helpI c; helpA t; helpA f]
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


let add_built_in_library (p : sourcespan program) : sourcespan program =
  let helpD (decls : sourcespan decl list) (fake_loc : sourcespan) : sourcespan decl list =
    let func_body = EApp("cinput", [], Native, fake_loc) in
    [DFun("input", [], func_body, fake_loc)]
    @ decls
  in
  match p with
  | Program(decls, body, loc) ->
    let new_decls = helpD decls loc in
    Program(new_decls, body, loc)
;;

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
    | EScIf(cond, _then, _else, _) ->
       let (cond_imm, cond_setup) = helpI cond in
       (CScIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
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
    | EScIf(cond, _then, _else, tag) ->
       let tmp = sprintf "scif_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [(tmp, CScIf(cond_imm, helpA _then, helpA _else, ()))])
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
  let rec setup_env (d : sourcespan decl list) (init_env : env_entry envt) : (env_entry envt) * (exn list) =
    match d with
    | [] -> (init_env, [])
    | DFun(fname, args, body, loc) :: tail ->
        let (tail_env, tail_errs) = (setup_env tail init_env) in
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
      | EScIf(cond, thn, els, _) -> raise (InternalCompilerError "EScIf is not in the egg-eater syntax")
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
  and wf_D (d : sourcespan decl) (env : env_entry envt) : exn list =
    match d with
    | DFun(fname, args, body, _) ->
        let flattened_args = bind_pairs args in
        let new_env = List.fold_left
          (fun accum_env arg_pair ->
            let (sym,loc) = arg_pair in
            (sym, Var(loc)) :: accum_env)
          env flattened_args
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
  | Program(decls, body, fake_loc) ->
      let init_env = [("cinput",Func(0,fake_loc))] in
      (* gather all functions into the env *)
      let (env, init_errs) = setup_env decls init_env in
      (* check decls *)
      let decl_errs =
        List.fold_left
          (fun (acc : (exn list)) decl -> ((wf_D decl env) @ acc))
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

let desugar_decl_arg_tups (p : sourcespan program) : sourcespan program =
  let gensym =
    let next = ref 0 in
    (fun name ->
      next := !next + 1;
      sprintf "%s_%d" name (!next)) in
  let rec helpD (d : sourcespan decl) =
    match d with
    | DFun(fname, args, body, loc) ->
        let (desugared_args, desugared_body) =
          List.fold_right
          (fun arg (args_acc, body_acc) ->
            begin
            match arg with
            | BBlank(_) -> (arg::args_acc, body_acc)
            | BName(_, _, _) -> (arg::args_acc, body_acc)
            | BTuple(binds, bloc) ->
                let new_arg_sym = gensym "tup$" in (* TODO better name? *)
                let new_body = ELet([(arg, EId(new_arg_sym,bloc), bloc)], body_acc, bloc) in
                let new_bind = BName(new_arg_sym,false,bloc) in
                (new_bind::args_acc, new_body)
            end)
          args ([], body) in
        DFun(fname, desugared_args, desugared_body, loc)
  in
  match p with
  | Program(decls, body, loc) ->
    let desugared_decls = List.map helpD decls in
    Program(desugared_decls, body, loc)

let desugar_let_bind_tups (p : sourcespan program) : sourcespan program =
  let gensym =
    let next = ref 0 in
    (fun name ->
      next := !next + 1;
      sprintf "%s_%d" name (!next)) in
  let rec helpBind (bnd : sourcespan bind) (body : sourcespan expr) (idx_in_parent : int) (parent_name : string) : (sourcespan expr) =
    match bnd with
      | BBlank(loc) -> ELet([(bnd, EGetItem(EId(parent_name, loc), ENumber(Int64.of_int idx_in_parent, loc), loc), loc)], body, loc)
      | BName(sym, bl, loc) -> ELet([(bnd, EGetItem(EId(parent_name, loc), ENumber(Int64.of_int idx_in_parent, loc), loc), loc)], body, loc)
      | BTuple(bnds, loc) ->
        let new_name = gensym "tup$" in
        let (new_body, _) = List.fold_left
          (fun (body_acc, idx) bnd ->
           let new_body = helpBind bnd body_acc idx new_name in (new_body, idx + 1))
           (body, 0)
           bnds in
        let new_lhs = BName(new_name, false, loc) in
        let new_rhs = EGetItem(EId(parent_name, loc), ENumber(Int64.of_int idx_in_parent, loc), loc) in
        ELet([(new_lhs, new_rhs, loc)], new_body, loc)

  and helpBindings (bindings : sourcespan binding list) (body : sourcespan expr) : sourcespan expr =
    match bindings with
    | [] -> body
    | ((bnd, rhs, loc) as bnding)::rest ->
      let rest_expr = helpBindings rest body in
      begin
      match bnd with
      (* todo (investigate)- I think we are splitting up lists of bindings into nested lets here *)
      | BBlank(loc) -> ELet([bnding], rest_expr, loc)
      | BName(_, _, _) -> ELet([bnding], rest_expr, loc)
      | BTuple(bnds, loc) ->
        let new_name = gensym "tup$" in
        let (new_body, _) = List.fold_left
          (fun (body_acc, idx) bnd ->
           let new_body = helpBind bnd body_acc idx new_name in (new_body, idx + 1))
           (rest_expr, 0)
           bnds in
        let new_lhs = BName(new_name, false, loc) in
        ELet([(new_lhs, rhs, loc)], new_body, loc)
      end
  and helpE (e : sourcespan expr) : sourcespan expr =
    match e with
    | ELet(bindings, body, loc) -> helpBindings bindings body
    | ESeq(lhs, rhs, loc) -> ESeq(helpE lhs, helpE rhs, loc)
    | ETuple(exprs, loc) -> ETuple(List.map helpE exprs, loc)
    | EGetItem(tup, idx, loc) -> EGetItem(helpE tup, helpE idx, loc)
    | ESetItem(tup, idx, newval, loc) -> ESetItem(helpE tup, helpE idx, helpE newval, loc)
    | EPrim1(op, expr, loc) -> EPrim1(op, helpE expr, loc)
    | EPrim2(op, lhs, rhs, loc) -> EPrim2(op, helpE lhs, helpE rhs, loc)
    | EIf(cond, thn, els, loc) -> EIf(helpE cond, helpE thn, helpE els, loc)
    | EScIf(cond, thn, els, loc) -> EScIf(helpE cond, helpE thn, helpE els, loc)
    | EApp(fname, args, ctype, loc) -> EApp(fname, List.map helpE args, ctype, loc)
    | _ -> e
  and helpD (d : sourcespan decl) : sourcespan decl =
    match d with
    | DFun(fname, args, body, loc) -> DFun(fname, args, helpE body, loc)
  in
  match p with
  | Program(decls, body, loc) ->
    let desugared_decls = List.map helpD decls in
    let desugared_body = helpE body in
    Program(desugared_decls, desugared_body, loc)
;;

let desugar_args_as_let_binds (p : sourcespan program) : sourcespan program =
  let rec help_decl (d : 'a decl) : sourcespan decl =
    match d with
    | DFun(fname, args, body, loc) ->
        (* purposely shadow the args with let bindings to prevent the potential
         * for the 'max' (or 'min) problem during tail recursion *)
        let arg_binds = List.fold_left
          (fun new_args_accum arg ->
            match arg with
            | BName(sym, _, loc) ->
                (arg, EId(sym, loc), loc) :: new_args_accum
            | BBlank _ -> new_args_accum
            | BTuple _ -> new_args_accum)
          [] args in
        let new_body = ELet(arg_binds, body, loc) in
        DFun(fname, args, new_body, loc)
  in
  match p with
  | Program(decls, body, loc) ->
      let rw_decls = List.map help_decl decls in
      Program(rw_decls, body, loc)
;;

let desugar_and_or (p : sourcespan program) : sourcespan program =
  let rec help_decl (d : sourcespan decl) : sourcespan decl =
    match d with
    | DFun(fname, args, body, loc) ->
        DFun(fname, args, help_expr body, loc)
  and help_expr (e : sourcespan expr) : sourcespan expr =
    match e with
    | EPrim2(op, lhs, rhs, loc) ->
       let lhs_untagged = help_expr lhs in
       let rhs_untagged = help_expr rhs in
       begin match op with
        (* (e1 && e2) -> (if !e1: false else: e2) *)
        | And -> EScIf(EPrim1(Not, lhs_untagged, loc), EBool(false, loc), rhs_untagged, loc)
        (* (e1 || e2) -> (if e1: true else: e2) *)
        | Or -> EScIf(lhs_untagged, EBool(true, loc), rhs_untagged, loc)
        | _ -> EPrim2(op, (help_expr lhs), (help_expr rhs), loc)
       end
    | ESeq(le, re, loc) -> ESeq(help_expr le, help_expr re, loc)
    | ETuple(exprs, loc) -> ETuple(List.map help_expr exprs, loc)
    | EGetItem(tup, idx, loc) -> EGetItem(help_expr tup, help_expr idx, loc)
    | ESetItem(tup, idx, rhs, loc) -> ESetItem(help_expr tup, help_expr idx, help_expr rhs, loc)
    | ELet(binds, body, loc) ->
        let rw_binds = List.map
          (fun (bind, rhs, loc) ->
            (bind, help_expr rhs, loc))
          binds in
        ELet(rw_binds, help_expr body, loc)
    | EPrim1(op, expr, loc) -> EPrim1(op, (help_expr expr), loc)
    | EIf(cond, thn, els, loc) ->
        EIf((help_expr cond), (help_expr thn), (help_expr els), loc)
    | EScIf _ -> raise (InternalCompilerError "EScIf is not in the egg-eater syntax")
    | EApp(fname, args, ct, loc) ->
        let rw_args = List.map help_expr args in
        EApp(fname, rw_args, ct, loc)
    | _ -> e
  in
  match p with
  | Program(decls, body, loc) ->
      let rw_decls = List.map help_decl decls in
      let rw_body = help_expr body in
      Program(rw_decls, rw_body, loc)
;;

let desugar_sequences (p : sourcespan program) : sourcespan program =
  let rec help_decl (d : sourcespan decl) : sourcespan decl =
    match d with
    | DFun(fname, args, body, loc) ->
        DFun(fname, args, help_expr body, loc)
  and help_expr (e : sourcespan expr) : sourcespan expr =
    match e with
    | ESeq(le, re, loc) ->
        let binding = (BBlank(loc), help_expr le, loc) in
        ELet([binding], help_expr re, loc)
    | ETuple(exprs, loc) -> ETuple(List.map help_expr exprs, loc)
    | EGetItem(tup, idx, loc) -> EGetItem(help_expr tup, help_expr idx, loc)
    | ESetItem(tup, idx, rhs, loc) -> ESetItem(help_expr tup, help_expr idx, help_expr rhs, loc)
    | ELet(binds, body, loc) ->
        let rw_binds = List.map
          (fun (bind, rhs, loc) ->
            (bind, help_expr rhs, loc))
          binds in
        ELet(rw_binds, help_expr body, loc)
    | EPrim1(op, expr, loc) -> EPrim1(op, (help_expr expr), loc)
    | EPrim2(op, lhs, rhs, loc) -> EPrim2(op, help_expr lhs, help_expr rhs, loc)
    | EIf(cond, thn, els, loc) ->
        EIf((help_expr cond), (help_expr thn), (help_expr els), loc)
    | EScIf(cond, thn, els, loc) ->
        EScIf((help_expr cond), (help_expr thn), (help_expr els), loc)
    | EApp(fname, args, ct, loc) ->
        let rw_args = List.map help_expr args in
        EApp(fname, rw_args, ct, loc)
    | _ -> e
  in
  match p with
  | Program(decls, body, loc) ->
      let rw_decls = List.map help_decl decls in
      let rw_body = help_expr body in
      Program(rw_decls, rw_body, loc)
;;

let desugar_print_to_app (p : sourcespan program) : sourcespan program =
  let rec help_decl (d : sourcespan decl) : sourcespan decl =
    match d with
    | DFun(fname, args, body, loc) ->
        DFun(fname, args, help_expr body, loc)
  and help_expr (e : sourcespan expr) : sourcespan expr =
    match e with
    | EPrim1(Print, expr, loc) -> EApp("print", [help_expr expr], Native, loc)
    | EPrim1(op, expr, loc) -> EPrim1(op, (help_expr expr), loc)
    | ESeq(le, re, loc) -> ESeq(help_expr le, help_expr re, loc)
    | ETuple(exprs, loc) -> ETuple(List.map help_expr exprs, loc)
    | EGetItem(tup, idx, loc) -> EGetItem(help_expr tup, help_expr idx, loc)
    | ESetItem(tup, idx, rhs, loc) -> ESetItem(help_expr tup, help_expr idx, help_expr rhs, loc)
    | ELet(binds, body, loc) ->
        let rw_binds = List.map
          (fun (bind, rhs, loc) ->
            (bind, help_expr rhs, loc))
          binds in
        ELet(rw_binds, help_expr body, loc)
    | EPrim2(op, lhs, rhs, loc) -> EPrim2(op, help_expr lhs, help_expr rhs, loc)
    | EIf(cond, thn, els, loc) ->
        EIf((help_expr cond), (help_expr thn), (help_expr els), loc)
    | EScIf(cond, thn, els, loc) ->
        EScIf((help_expr cond), (help_expr thn), (help_expr els), loc)
    | EApp(fname, args, ct, loc) ->
        let rw_args = List.map help_expr args in
        EApp(fname, rw_args, ct, loc)
    | _ -> e
  in
  match p with
  | Program(decls, body, loc) ->
      let rw_decls = List.map help_decl decls in
      let rw_body = help_expr body in
      Program(rw_decls, rw_body, loc)
;;



(* Desugaring:
 * and/or rewrite
 * let bindings with tuple on the LHS
 * tuples as func args
 * add let binding for every func arg (to prevent tail-recursion overwrite)
 * sequence -> let bindings with "_"
*)
let desugar (p : sourcespan program) : sourcespan program =
  desugar_sequences
  (desugar_and_or
  (desugar_args_as_let_binds
  (* "desugar_decl_arg_tups" comes before "desugar_let_bind_tups" to make sure we
   * don't unnecessarily duplicate the "tup" variable we use as a func arg during
   * the "desugar_decl_arg_tups" phase. *)
  (desugar_let_bind_tups
  (desugar_decl_arg_tups
  (desugar_print_to_app p)))))
;;

(* ASSUMES that the program has been alpha-renamed and all names are unique *)
let naive_stack_allocation (prog: tag aprogram) : tag aprogram * arg envt =
  let rec help_decl (decl : tag adecl) (env : arg envt) : arg envt =
    match decl with
    | ADFun(fname, args, body, _) ->
        let args_with_idx = List.mapi (fun i arg -> (arg, RegOffset((i + 2)*word_size, RBP))) args in
        let new_env = List.fold_left (fun accum_env cell -> cell :: accum_env) env args_with_idx in
        let (decl_env, _) = help_aexpr body 1 new_env in
        decl_env
  and help_aexpr (body : tag aexpr) (si : int) (env : arg envt) : arg envt * int =
    match body with
    | ALet(sym, bind, body, _) ->
        let newenv = (sym, RegOffset(~-si*word_size, RBP)) :: env in
        let (bindenv, newsi) = help_cexpr bind (si+1) newenv in
        help_aexpr body newsi bindenv
    | ACExpr(cexpr) -> help_cexpr cexpr si env
  and help_cexpr (expr : tag cexpr) (si : int) (env : arg envt) : arg envt * int =
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
  in
  match prog with
  | AProgram(decls, body, _) ->
      let decl_env =
        List.fold_left (fun accum_env decl -> help_decl decl accum_env) [] decls in
      let (prog_env, _) = help_aexpr body 1 decl_env in
      (prog, prog_env)
;;


(* Compiled Type Checking *)
let check_rax_for_num (err_lbl : string) : instruction list =
  [
   (* This "test" trick depends on num_tag being 0. R8 used because Test doesn't support imm64 *)
   ILineComment("check_rax_for_num (" ^ err_lbl ^ ")");
   IMov(Reg(R8), HexConst(num_tag_mask));
   ITest(Reg(RAX), Reg(R8));
   IJnz(err_lbl);
  ]

let check_rax_for_bool (err_lbl : string) : instruction list =
  [
   (* Operate on temp register R8 instead of RAX. This is because we call AND
    * on the register, which will alter the value. We want to preserve the value
    * in RAX, hence we operate on R8 instead. R9 is used as intermediate because
      And, Cmp don't work on imm64s *)
   ILineComment("check_rax_for_bool (" ^ err_lbl ^ ")");
   IMov(Reg(R8), Reg(RAX));
   IMov(Reg(R9), HexConst(bool_tag_mask));
   IAnd(Reg(R8), Reg(R9));
   IMov(Reg(R9), HexConst(bool_tag));
   ICmp(Reg(R8), Reg(R9));
   IJnz(err_lbl);
  ]

let check_for_overflow = [IJo("err_OVERFLOW")]


let check_rax_for_tup (err_lbl : string) : instruction list =
  [
   (* Operate on temp register R8 instead of RAX. This is because we call AND
    * on the register, which will alter the value. We want to preserve the value
    * in RAX, hence we operate on R8 instead. R9 is used as intermediate because
      And, Cmp don't work on imm64s *)
   ILineComment("check_rax_for_tup (" ^ err_lbl ^ ")");
   IMov(Reg(R8), Reg(RAX));
   IMov(Reg(R9), HexConst(tup_tag_mask));
   IAnd(Reg(R8), Reg(R9));
   IMov(Reg(R9), HexConst(tup_tag));
   ICmp(Reg(R8), Reg(R9));
   IJne(err_lbl);
  ]

let check_rax_for_nil (err_lbl : string) : instruction list =
  [
   ILineComment("check_rax_for_nil (" ^ err_lbl ^ ")");
   IMov(Reg(R8), const_nil);
   ICmp(Reg(RAX), Reg(R8));
   IJe(err_lbl);
  ]


(* RAX should be the snakeval of the index (in a tuple)*)
(* DO NOT MODIFY RAX *)
let check_rax_for_tup_smaller (err_lbl : string) : instruction list =
  [
   ILineComment("check_rax_for_tup_smaller (" ^ err_lbl ^ ")");
   ICmp(Reg(RAX), Const(0L));
   (* no temp register because imm32 0 will be "sign-extended to imm64", which should still be 0 *)
   IJl(err_lbl);
  ]


(* RAX should be the snakeval of the index (in a tuple)*)
(* DO NOT MODIFY RAX *)
let check_rax_for_tup_bigger (tup_address : arg) (err_lbl : string) : instruction list =
  [
   (* R8 is used as intermediate because Cmp don't work on imm64s *)
   ILineComment("check_rax_for_tup_bigger (" ^ err_lbl ^ ")");
   IMov(Reg(R8), tup_address);
   ISub(Reg(R8), Const(1L)); (* convert from snake val address -> machine address *)
   IMov(Reg(R8), RegOffset(0, R8)); (* load the tup length into RAX *)
   ICmp(Reg(RAX), Reg(R8));
   IJge(err_lbl);
  ]


let compile_fun_prelude (fun_name : string) (args : string list) (env : arg envt) (num_local_vars : int): instruction list =
  [
    ILabel(fun_name);
    IPush(Reg(RBP));
    IMov(Reg(RBP), Reg(RSP));
    (* Don't use temp register here because we assume the RHS will never be very big *)
    ISub(Reg(RSP), Const(Int64.of_int (word_size * num_local_vars)))  (* allocates stack space for all local vars *)
  ]

let compile_fun_postlude (num_local_vars : int) : instruction list =
  [
    IMov(Reg(RSP), Reg(RBP));  (* Move stack to how it was at start of this function *)
    IPop(Reg(RBP));
    IRet;
  ]





let rec compile_aexpr (e : tag aexpr) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  match e with
  | ALet(id, bind, body, _) ->
    let compiled_bind = compile_cexpr bind env num_args false in
    let dest = (find env id) in
    let compiled_body = compile_aexpr body env num_args is_tail in
    [ILineComment(sprintf "Let: %s" id)]
    @ compiled_bind
    @ [IMov(dest, Reg(RAX))]
    @ compiled_body
  | ACExpr(expr) -> (compile_cexpr expr env num_args is_tail)
and compile_cexpr (e : tag cexpr) (env : arg envt) (num_args : int) (is_tail : bool) =
  match e with
  | CIf(cond, thn, els, tag) ->
     let cond_reg = compile_imm cond env in
     let lbl_comment = sprintf "if_%d" tag in
     let lbl_thn = sprintf "if_then_%d" tag in
     let lbl_els = sprintf "if_else_%d" tag in
     let lbl_done = sprintf "if_done_%d" tag in
     (* check cond for boolean val *)
     [ILineComment(lbl_comment)]
     @ [IMov(Reg(RAX), cond_reg)]
     @ (check_rax_for_bool "err_IF_NOT_BOOL")
     (* test for RAX == true *)
     (* need to use temp register R8 because Test cannot accept imm64 *)
     @ [IMov(Reg(R8), bool_mask)]
     @ [ITest(Reg(RAX), Reg(R8))]
     @ [IJz(lbl_els)]

     @ [ILabel(lbl_thn)]
     @ (compile_aexpr thn env num_args is_tail)
     @ [IJmp(lbl_done)]

     @ [ILabel(lbl_els)]
     @ (compile_aexpr els env num_args is_tail)
     @ [ILabel(lbl_done)]
  | CScIf(cond, thn, els, tag) ->
     let cond_reg = compile_imm cond env in
     let lbl_comment = sprintf "scif_%d" tag in
     let lbl_thn = sprintf "scif_then_%d" tag in
     let lbl_els = sprintf "scif_else_%d" tag in
     let lbl_done = sprintf "scif_done_%d" tag in
     (* check cond for boolean val *)
     [ILineComment(lbl_comment)]
     @ [IMov(Reg(RAX), cond_reg)]
     @ (check_rax_for_bool "err_LOGIC_NOT_BOOL")
     (* test for RAX == true *)
     (* need to use temp register R8 because Test cannot accept imm64 *)
     @ [IMov(Reg(R8), bool_mask)]
     @ [ITest(Reg(RAX), Reg(R8))]
     @ [IJz(lbl_els)]

     @ [ILabel(lbl_thn)]
     (* LHS is compiled before RHS, so definitely not tail position *)
     @ (compile_aexpr thn env num_args false)
     @ [IJmp(lbl_done)]

     @ [ILabel(lbl_els)]
     (* Since we check that result is bool, RHS is also not in tail position *)
     @ (compile_aexpr els env num_args false)
     @ (check_rax_for_bool "err_LOGIC_NOT_BOOL")
     @ [ILabel(lbl_done)]
  | CPrim1(op, body, tag) -> 
    let body_imm = compile_imm body env in
     begin match op with
       | Add1 ->
           [IMov(Reg(RAX), body_imm)]
           @ (check_rax_for_num "err_ARITH_NOT_NUM")
           @ [IAdd(Reg(RAX), Const(2L))]
           @ check_for_overflow
       | Sub1 ->
           [IMov(Reg(RAX), body_imm)]
           @ (check_rax_for_num "err_ARITH_NOT_NUM")
           @ [ISub(Reg(RAX), Const(2L))]
           @ check_for_overflow
        | Print -> raise (InternalCompilerError "Impossible: 'print' should be rewritten to a function application")
        | IsBool ->
          let true_lbl = sprintf "is_bool_true_%d" tag in
          let false_lbl = sprintf "is_bool_false_%d" tag in
          let done_lbl = sprintf "is_bool_done_%d" tag in
          [
           IMov(Reg(RAX), body_imm);
           (* Don't need to save RAX on the stack because we overwrite the
            * value with true/false later. R8 used because And, Cmp don't support imm64 *)
           IMov(Reg(R8), HexConst(bool_tag_mask));
           IAnd(Reg(RAX), Reg(R8));
           IMov(Reg(R8), HexConst(bool_tag));
           ICmp(Reg(RAX), Reg(R8));
           IJz(true_lbl);
           (* case not bool *)
           ILabel(false_lbl);
           IMov(Reg(RAX), const_false);
           IJmp(done_lbl);
           (* case is a bool *)
           ILabel(true_lbl);
           IMov(Reg(RAX), const_true);
           (* done *)
           ILabel(done_lbl);
          ]
        | IsNum ->
          let true_lbl = sprintf "is_num_true_%d" tag in
          let false_lbl = sprintf "is_num_false_%d" tag in
          let done_lbl = sprintf "is_num_done_%d" tag in
          [
           IMov(Reg(RAX), body_imm);
           (* This "test" trick depends on num_tag being 0. R8 used because Test doesn't support imm64 *)
           IMov(Reg(R8), HexConst(num_tag_mask));
           ITest(Reg(RAX), Reg(R8));
           IJz(true_lbl);
           (* case not num *)
           ILabel(false_lbl);
           IMov(Reg(RAX), const_false);
           IJmp(done_lbl);
           (* case is a num *)
           ILabel(true_lbl);
           IMov(Reg(RAX), const_true);
           (* done *)
           ILabel(done_lbl);
          ]
        | Not ->
           [IMov(Reg(RAX), body_imm)]
           @ (check_rax_for_bool "err_LOGIC_NOT_BOOL")
           (* need to use temp register R8 because Xor cannot accept imm64 *)
           @ [IMov(Reg(R8), bool_mask)]
           @ [IXor(Reg(RAX), Reg(R8))]
        | PrintStack ->
            raise (NotYetImplemented "PrintStack not yet implemented")
        | IsTuple ->
          let true_lbl = sprintf "is_tup_true_%d" tag in
          let false_lbl = sprintf "is_tup_false_%d" tag in
          let done_lbl = sprintf "is_tup_done_%d" tag in
          [
           IMov(Reg(RAX), body_imm);
           (* Don't need to save RAX on the stack because we overwrite the
            * value with true/false later. R8 used because And, Cmp don't support imm64 *)
           IMov(Reg(R8), HexConst(tup_tag_mask));
           IAnd(Reg(RAX), Reg(R8));
           IMov(Reg(R8), HexConst(tup_tag));
           ICmp(Reg(RAX), Reg(R8));
           IJz(true_lbl);
           (* case not tup *)
           ILabel(false_lbl);
           IMov(Reg(RAX), const_false);
           IJmp(done_lbl);
           (* case is a tup *)
           ILabel(true_lbl);
           IMov(Reg(RAX), const_true);
           (* done *)
           ILabel(done_lbl);
          ]
     end
  | CPrim2(op, lhs, rhs, tag) ->
     let lhs_reg = compile_imm lhs env in
     let rhs_reg = compile_imm rhs env in
     begin match op with
      | Plus ->
         (* check rhs for numerical val *)
         [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_num "err_ARITH_NOT_NUM")
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num "err_ARITH_NOT_NUM")
         (* need to use a temp register because ADD does not properly handle imm64 (for overflow) *)
         @ [IMov(Reg(R8), rhs_reg)]
         @ [IAdd(Reg(RAX), Reg(R8))]
         @ check_for_overflow
      | Minus ->
         (* check rhs for numerical val *)
         [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_num "err_ARITH_NOT_NUM")
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num "err_ARITH_NOT_NUM")
         (* need to use a temp register because SUB does not properly handle imm64 (for overflow) *)
         @ [IMov(Reg(R8), rhs_reg)]
         @ [ISub(Reg(RAX), Reg(R8))]
         @ check_for_overflow
      | Times ->
         (* check rhs for numerical val *)
         [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_num "err_ARITH_NOT_NUM")
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num "err_ARITH_NOT_NUM")
         @ [ISar(Reg(RAX), Const(1L))]
         (* need to use a temp register because IMUL does not properly handle imm64 (for overflow) *)
         @ [IMov(Reg(R8), rhs_reg)]
         @ [IMul(Reg(RAX), Reg(R8))]
         @ check_for_overflow
      | And -> raise (InternalCompilerError "Impossible: 'and' should be rewritten")
      | Or -> raise (InternalCompilerError "Impossible: 'or' should be rewritten")
      | Greater ->
         let lbl_false = sprintf "greater_false_%d" tag in
         let lbl_done = sprintf "greater_done_%d" tag in

         (* check rhs for numerical val *)
         [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_num "err_COMP_NOT_NUM")
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num "err_COMP_NOT_NUM")

         (* need to use temp register R8 because Test cannot accept imm64 *)
         @ [IMov(Reg(R8), rhs_reg)]
         @ [ICmp(Reg(RAX), Reg(R8))]
         @ [IMov(Reg(RAX), const_true)]
         @ [IJg(lbl_done)]

         @ [ILabel(lbl_false)]
         @ [IMov(Reg(RAX), const_false)]

         @ [ILabel(lbl_done)]
      | GreaterEq ->
         let lbl_false = sprintf "greater_eq_false_%d" tag in
         let lbl_done = sprintf "greater_eq_done_%d" tag in

         (* check rhs for numerical val *)
         [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_num "err_COMP_NOT_NUM")
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num "err_COMP_NOT_NUM")

         (* need to use temp register R8 because Test cannot accept imm64 *)
         @ [IMov(Reg(R8), rhs_reg)]
         @ [ICmp(Reg(RAX), Reg(R8))]
         @ [IMov(Reg(RAX), const_true)]
         @ [IJge(lbl_done)]

         @ [ILabel(lbl_false)]
         @ [IMov(Reg(RAX), const_false)]

         @ [ILabel(lbl_done)]
      | Less ->
         let lbl_false = sprintf "less_false_%d" tag in
         let lbl_done = sprintf "less_done_%d" tag in

         (* check rhs for numerical val *)
         [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_num "err_COMP_NOT_NUM")
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num "err_COMP_NOT_NUM")

         (* need to use temp register R8 because Test cannot accept imm64 *)
         @ [IMov(Reg(R8), rhs_reg)]
         @ [ICmp(Reg(RAX), Reg(R8))]
         @ [IMov(Reg(RAX), const_true)]
         @ [IJl(lbl_done)]

         @ [ILabel(lbl_false)]
         @ [IMov(Reg(RAX), const_false)]

         @ [ILabel(lbl_done)]
      | LessEq ->
         let lbl_false = sprintf "less_eq_false_%d" tag in
         let lbl_done = sprintf "less_eq_done_%d" tag in

         (* check rhs for numerical val *)
         [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_num "err_COMP_NOT_NUM")
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num "err_COMP_NOT_NUM")

         (* need to use temp register R8 because Test cannot accept imm64 *)
         @ [IMov(Reg(R8), rhs_reg)]
         @ [ICmp(Reg(RAX), Reg(R8))]
         @ [IMov(Reg(RAX), const_true)]
         @ [IJle(lbl_done)]

         @ [ILabel(lbl_false)]
         @ [IMov(Reg(RAX), const_false)]

         @ [ILabel(lbl_done)]
      | Eq ->
         let lbl_false = sprintf "eq_false_%d" tag in
         let lbl_done = sprintf "eq_done_%d" tag in

         [IMov(Reg(RAX), lhs_reg)]

         (* need to use temp register R8 because Test cannot accept imm64 *)
         @ [IMov(Reg(R8), rhs_reg)]
         @ [ICmp(Reg(RAX), Reg(R8))]
         @ [IMov(Reg(RAX), const_true)]
         @ [IJe(lbl_done)]

         @ [ILabel(lbl_false)]
         @ [IMov(Reg(RAX), const_false)]

         @ [ILabel(lbl_done)]
     end
  | CApp(fname, args, ct, _) ->
    let f_num_args = (List.length args) in
    let is_even_f_num_args = f_num_args mod 2 == 0 in
    let padding = (if is_even_f_num_args then [] else [IMov(Reg(R8), HexConst(0xF0F0F0F0L)); IPush(Reg(R8))]) in
    (* Push the args onto stack in reverse order *)
    let args_rev = List.rev args in
    let f_num_args_passed = f_num_args + (if is_even_f_num_args then 0 else 1) in
    let is_even_num_args = num_args mod 2 == 0 in
    let num_args_passed = num_args + (if is_even_num_args then 0 else 1) in
    (* Technically we allow tailcall optimization with 1 more arg if this function has odd num of args *)
    begin match ct with
    | Native ->
        if f_num_args > 1 then
          raise (InternalCompilerError "Our compiler does not support native calls with more than 1 arg")
        else
          let add_arg =
            if f_num_args = 1
            then
              let arg = List.hd args in
              let compiled_arg = (compile_imm arg env) in
              [IMov(Reg(RDI), compiled_arg)]
            else [] in
          add_arg
          @ [ICall(fname)]
    | Snake ->
        if is_tail && (f_num_args <= num_args_passed) then
            let (compiled_args, _) = List.fold_left
                           (fun accum_instrs_idx arg ->
                              let compiled_imm = (compile_imm arg env) in
                              let (accum_instrs, i) = accum_instrs_idx in
                              (* Use temp register because can't push imm64 directly *)
                              (accum_instrs
                                @ [IMov(Reg(R8), compiled_imm);
                                   IMov(RegOffset((i + 2) * word_size, RBP), Reg(R8))],
                               i + 1))
                           ([], 0)
                           args
                           in
            let body_label = sprintf "%s_body" fname in
            compiled_args @ [IJmp(body_label)]
        else
            let compiled_args = List.fold_left
                           (fun accum_instrs arg ->
                              let compiled_imm = (compile_imm arg env) in
                              (* Use temp register because can't push imm64 directly *)
                              accum_instrs @ [IMov(Reg(R8), compiled_imm);
                                              IPush(Sized(QWORD_PTR, Reg(R8)))])
                           []
                           args_rev
                           in
            let padded_comp_args = padding @ compiled_args in
            padded_comp_args
            @
            [
            ICall(fname);
            (* Don't use temp register here because we assume the RHS will never be very big *)
            IAdd(Reg(RSP), Const(Int64.of_int (word_size * f_num_args_passed)));
            ]
    | _ -> raise (InternalCompilerError "Invalid function application call type")
    end
  | CImmExpr(expr) -> [IMov(Reg(RAX), (compile_imm expr env))]
  | CTuple(elems, _) -> 
      let tup_size = List.length elems in
      let need_padding = tup_size mod 2 == 1 in
      let padding_val = HexConst(0xF0F0F0F0L) in
      let padding =
        if need_padding then []
        else
          let offs = tup_size + 1 in
          [IMov(Reg(R8), padding_val); IMov(RegOffset(offs*word_size, R15), Reg(R8))] in
      let next_heap_loc = tup_size + 1 + ((1+tup_size) mod 2) in

      (* store the tuple size on the heap *)
      [IMov(Reg(R8), Const(Int64.of_int tup_size)); IMov(RegOffset(0, R15), Reg(R8))]
      (* store each tuple element on the heap *)
      @ List.flatten
          (List.mapi
            (fun i e ->
              let arg = compile_imm e env in
              let offs = i + 1 in
              [IMov(Reg(R8), arg); IMov(RegOffset(offs*word_size, R15), Reg(R8))])
            elems)
      @ padding
      (* return the pointer to the tuple, make it a snakeval *)
      @ [IMov(Reg(RAX), Reg(R15)); IAdd(Reg(RAX), Const(1L))]
      (* increment the heap ptr *)
      @ [IMov(Reg(R8), Const(Int64.of_int (next_heap_loc * word_size))); IAdd(Reg(R15), Reg(R8))]
  | CGetItem(tup, i, _) ->
      let tup_address = compile_imm tup env in
      let idx = compile_imm i env in

      (* first, do runtime error checking *)
      [IMov(Reg(RAX), tup_address)] (* move tuple address (snakeval) into RAX *)
      @ (check_rax_for_tup "err_GET_NOT_TUPLE")
      @ (check_rax_for_nil "err_NIL_DEREF")
      @ [IMov(Reg(RAX), idx)] (* move the idx (snakeval) into RAX *)
      @ (check_rax_for_num "err_TUP_IDX_NOT_NUM")
      @ [ISar(Reg(RAX), Const(1L))] (* convert from snakeval -> int *)
      @ (check_rax_for_tup_smaller "err_GET_LOW_INDEX")
      @ (check_rax_for_tup_bigger tup_address "err_GET_HIGH_INDEX")

      (* passed checks, now do actual 'get' *)
      @ [IMov(Reg(RAX), tup_address)] (* move tuple address back into RAX *)
      @ [ISub(Reg(RAX), Const(1L))] (* convert from snake val address -> machine address *)
      @ [IMov(Reg(R8), idx)] (* move the idx (snakeval) into R8 *)
      @ [ISar(Reg(R8), Const(1L))] (* convert from snake val -> int *)
      @ [IAdd(Reg(R8), Const(1L))] (* add 1 to the offset to bypass the tup size *)
      @ [IMov(Reg(RAX), RegOffsetReg(RAX,R8,word_size,0))]
  | CSetItem(tup, i, r, _) ->
      let tup_address = compile_imm tup env in
      let idx = compile_imm i env in
      let rhs = compile_imm r env in

      (* first, do runtime error checking *)
      [IMov(Reg(RAX), tup_address)] (* move tuple address (snakeval) into RAX *)
      @ (check_rax_for_tup "err_GET_NOT_TUPLE")
      @ (check_rax_for_nil "err_NIL_DEREF")
      @ [IMov(Reg(RAX), idx)] (* move the idx (snakeval) into RAX *)
      @ (check_rax_for_num "err_TUP_IDX_NOT_NUM")
      @ [ISar(Reg(RAX), Const(1L))] (* convert from snakeval -> int *)
      @ (check_rax_for_tup_smaller "err_GET_LOW_INDEX")
      @ (check_rax_for_tup_bigger tup_address "err_GET_HIGH_INDEX")

      (* passed checks, now do actual 'set' *)
      @ [IMov(Reg(RAX), tup_address)] (* move tuple address (snakeval) into RAX *)
      @ [ISub(Reg(RAX), Const(1L))] (* convert from snake val -> address *)
      @ [IMov(Reg(R8), idx)] (* move the idx (* snakeval *) into R8 *)
      @ [ISar(Reg(R8), Const(1L))] (* convert from snake val -> int *)
      @ [IAdd(Reg(R8), Const(1L))] (* add 1 to the offset to bypass the tup size *)
      @ [IMov(Reg(R11), rhs)]
      @ [IMov(RegOffsetReg(RAX,R8,word_size,0), Reg(R11))]
      @ [IAdd(Reg(RAX), Const(1L))] (* convert the tuple address back to a snakeval *)
and compile_imm e (env : arg envt) : arg =
  match e with
  | ImmNum(n, _) -> Const(Int64.shift_left n 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)
  | ImmNil(_) -> const_nil


let compile_decl (d : tag adecl) (env : arg envt): instruction list =
  match d with
  | ADFun(fname, args, body, _) ->
    let num_body_vars = (deepest_stack body env) in
    let prelude = compile_fun_prelude fname args env num_body_vars in
    let compiled_body = compile_aexpr body env (List.length args) true in
    let postlude = compile_fun_postlude num_body_vars in
    let body_label = sprintf "%s_body" fname in
    prelude @ [ILabel(body_label)] @ compiled_body @ postlude

(*
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

;;*)



let compile_prog ((anfed : tag aprogram), (env : arg envt)) : string =
  match anfed with
  | AProgram(decls, body, _) ->
      let heap_start = [
          ILineComment("heap start");
          IInstrComment(IMov(Reg(heap_reg), Reg(List.nth first_six_args_registers 0)), "Load heap_reg with our argument, the heap pointer");
          IInstrComment(IAdd(Reg(heap_reg), Const(15L)), "Align it to the nearest multiple of 16");
          IInstrComment(IAnd(Reg(heap_reg), HexConst(0xFFFFFFFFFFFFFFF0L)), "by adding no more than 15 to it")
        ] in
      let compiled_decls =
        List.fold_left
          (fun accum_instrs decl ->
            accum_instrs
            (* basically a line of whitespace between function decls *)
            @ [ILineComment("")]
            @ (compile_decl decl env))
          [] decls in
      let num_prog_body_vars = (deepest_stack body env) in
      let compiled_body = (compile_aexpr body env 0 false) in
      let prelude =
        "section .text
extern error
extern print
extern cinput
global our_code_starts_here" in
      let stack_setup = [
          ILabel("our_code_starts_here");
          IPush(Reg(RBP));
          IMov(Reg(RBP), Reg(RSP));
          ISub(Reg(RSP), Const(Int64.of_int (word_size * num_prog_body_vars)))  (* allocates stack space for all local vars *)
        ] in
      let postlude = [
          ILabel("program_done");
          IAdd(Reg(RSP), Const(Int64.of_int (word_size * num_prog_body_vars)));  (* Undoes the allocation *)
          IPop(Reg(RBP));
          IRet;

          (* Error Labels *)
          ILabel("err_COMP_NOT_NUM");
          IMov(Reg(RDI), Const(err_COMP_NOT_NUM));
          ICall("error");
          IJmp("program_done");

          ILabel("err_ARITH_NOT_NUM");
          IMov(Reg(RDI), Const(err_ARITH_NOT_NUM));
          ICall("error");
          IJmp("program_done");

          ILabel("err_LOGIC_NOT_BOOL");
          IMov(Reg(RDI), Const(err_LOGIC_NOT_BOOL));
          ICall("error");
          IJmp("program_done");

          ILabel("err_IF_NOT_BOOL");
          IMov(Reg(RDI), Const(err_IF_NOT_BOOL));
          ICall("error");
          IJmp("program_done");

          ILabel("err_OVERFLOW");
          IMov(Reg(RDI), Const(err_OVERFLOW));
          ICall("error");
          IJmp("program_done");

          ILabel("err_GET_NOT_TUPLE");
          IMov(Reg(RDI), Const(err_GET_NOT_TUPLE));
          ICall("error");
          IJmp("program_done");

          ILabel("err_GET_LOW_INDEX");
          IMov(Reg(RDI), Const(err_GET_LOW_INDEX));
          ICall("error");
          IJmp("program_done");

          ILabel("err_GET_HIGH_INDEX");
          IMov(Reg(RDI), Const(err_GET_HIGH_INDEX));
          ICall("error");
          IJmp("program_done");

          ILabel("err_NIL_DEREF");
          IMov(Reg(RDI), Const(err_NIL_DEREF));
          ICall("error");
          IJmp("program_done");

          ILabel("err_TUP_IDX_NOT_NUM");
          IMov(Reg(RDI), Const(err_TUP_IDX_NOT_NUM));
          ICall("error");
          IJmp("program_done");
        ] in
      let decl_assembly_string = (to_asm compiled_decls) in
      let body_assembly_string = (to_asm (stack_setup @ heap_start @ compiled_body @ postlude)) in
      sprintf "%s%s%s\n" prelude decl_assembly_string body_assembly_string 


let run_if should_run f =
  if should_run then f else no_op_phase
;;

(* We chose to put the desugar phase after the well_formed check to make sure we spit
 * out the correct error location for ill-formed programs.  We choose to desugar before
 * ANFing because the desugar phase is not guaranteed to perform ANFing, therefore we
 * would need to call ANF a second time if we desugared after ANFing.  Tagging and
 * renaming needs to happen before ANFing, so we desugar before these two phases because
 * desugaring would invalidate both tagging and renaming.  Note: tagging and renaming
 * is not a prerequisite to desugaring.
 * *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_phase built_in_library add_built_in_library)
  |> (add_err_phase well_formed is_well_formed)
  (* Invariant: EScIf is not part of the AST *)
  |> (add_phase desugared desugar)
  (* Invariants:
    * 1. EPrim2's should never have "and" or "or" operators
    * 2. Every bind to a DFun will be shadowed in a ELet in the body.  This will
    *     avoid the "min/max" tail-recursion problem; see the comment inside
    *     desugar_args_as_let_binds for more details.
    * 3. ELet's will never have BTuple's in the receiving position (the lhs).
    * 4. The binds (arguments) to each DFun will never be an BTuple.
    * 5. There will be no ESeq's in our AST.
    * *)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename_and_tag)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase locate_bindings naive_stack_allocation)
  |> (add_phase result compile_prog)
;;
