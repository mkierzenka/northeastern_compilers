open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
(* Add at least one of these two *)
       
type 'a envt = (string * 'a) list

(* Our envs track existence+location of either a var (let binding) or function with arity *)
type env_entry =
  | Id of sourcespan
;;

let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1(_, e, _) -> is_imm e
  | EPrim2(_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet(binds, body, _) ->
     List.for_all (fun (_, e, _) -> is_anf e) binds
     && is_anf body
  | EIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | EScIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | _ -> is_imm e
and is_imm e =
  match e with
  | ENumber _ -> true
  | EBool _ -> true
  | EId _ -> true
  | _ -> false
;;

let const_true       = HexConst(0xFFFFFFFFFFFFFFFFL)
let const_false      = HexConst(0x7FFFFFFFFFFFFFFFL)
let bool_mask        = HexConst(0x8000000000000000L)
let bool_tag         = 0x0000000000000007L
let bool_tag_mask    = 0x0000000000000007L
let num_tag          = 0x0000000000000000L
let num_tag_mask     = 0x0000000000000001L
let closure_tag      = 0x0000000000000005L
let closure_tag_mask = 0x0000000000000007L
let tuple_tag        = 0x0000000000000001L
let tuple_tag_mask   = 0x0000000000000007L
let const_nil        = HexConst(tuple_tag)

let err_COMP_NOT_NUM     = 1L
let err_ARITH_NOT_NUM    = 2L
let err_LOGIC_NOT_BOOL   = 3L
let err_IF_NOT_BOOL      = 4L
let err_OVERFLOW         = 5L
let err_GET_NOT_TUPLE    = 6L
let err_GET_LOW_INDEX    = 7L
let err_GET_HIGH_INDEX   = 8L
let err_GET_NOT_NUM      = 9L
let err_NIL_DEREF        = 10L
let err_OUT_OF_MEMORY    = 11L
let err_SET_NOT_TUPLE    = 12L
let err_SET_LOW_INDEX    = 13L
let err_SET_NOT_NUM      = 14L
let err_SET_HIGH_INDEX   = 15L
let err_CALL_NOT_CLOSURE = 16L
let err_CALL_ARITY_ERR   = 17L
let err_BAD_INPUT        = 18L
let err_TUP_IDX_NOT_NUM  = 19L


let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]
let heap_reg = R15
let scratch_reg = R11

module StringSet = Set.Make(String)

(* You may find some of these helpers useful *)

let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y,v)::rest ->
     if y = x then v else find rest x

let count_vars e =
  let rec helpA e =
    match e with
    | ASeq(e1, e2, _) -> max (helpC e1) (helpA e2)
    | ALet(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
    | ALetRec(binds, body, _) ->
       (List.length binds) + List.fold_left max (helpA body) (List.map (fun (_, rhs) -> helpC rhs) binds)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf(_, t, f, _) -> max (helpA t) (helpA f)
    | CScIf(_, t, f, _) -> max (helpA t) (helpA f)
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

let rename_and_tag (p : tag program) : tag program =
  let rec rename env p =
    match p with
    | Program([], body, tag) -> Program([], helpE [] body, tag)
    | _ -> raise (InternalCompilerError "(R&T) Top-level declarations should have been desugared away")
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
  and helpBG env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a)::bindings ->
       let (b', env') = helpB env b in
       let e' = helpE env e in
       let (bindings', env'') = helpBG env' bindings in
       ((b', e', a)::bindings', env'')
  and helpE env e =
    match e with
    | ESeq(e1, e2, tag) -> ESeq(helpE env e1, helpE env e2, tag)
    | ETuple(es, tag) -> ETuple(List.map (helpE env) es, tag)
    | EGetItem(e, idx, tag) -> EGetItem(helpE env e, helpE env idx, tag)
    | ESetItem(e, idx, newval, tag) -> ESetItem(helpE env e, helpE env idx, helpE env newval, tag)
    | EPrim1(op, arg, tag) -> EPrim1(op, helpE env arg, tag)
    | EPrim2(op, left, right, tag) -> EPrim2(op, helpE env left, helpE env right, tag)
    | EIf(c, t, f, tag) -> EIf(helpE env c, helpE env t, helpE env f, tag)
    | EScIf(c, t, f, tag) -> EScIf(helpE env c, helpE env t, helpE env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId(name, tag) ->
       (try
         EId(find env name, tag)
       with InternalCompilerError _ -> e)
    | EApp(func, args, native, tag) ->
       let func = helpE env func in
       let call_type =
         (* TODO: If you want, try to determine whether func is a known function name, and if so,
            whether it's a Snake function or a Native function *)
         Snake in
       EApp(func, List.map (helpE env) args, call_type, tag)
    | ELet(binds, body, tag) ->
       let (binds', env') = helpBG env binds in
       let body' = helpE env' body in
       ELet(binds', body', tag)
    | ELetRec(bindings, body, tag) ->
       let (revbinds, env) = List.fold_left (fun (revbinds, env) (b, e, t) ->
                                 let (b, env) = helpB env b in ((b, e, t)::revbinds, env)) ([], env) bindings in
       let bindings' = List.fold_left (fun bindings (b, e, tag) -> (b, helpE env e, tag)::bindings) [] revbinds in
       let body' = helpE env body in
       ELetRec(bindings', body', tag)
    | ELambda(binds, body, tag) ->
       let (binds', env') = helpBS env binds in
       let body' = helpE env' body in
       ELambda(binds', body', tag)
  in (rename [] p)
;;

(* Returns the stack-index (in words) of the deepest stack index used for any 
   of the variables in this expression *)
let rec deepest_stack e env =
  let rec helpA e =
    match e with
    | ALet(name, bind, body, _) -> List.fold_left max 0 [name_to_offset name; helpC bind; helpA body]
    | ALetRec(binds, body, _) -> List.fold_left max (helpA body) (List.map (fun (name, bind) -> (max (helpC bind) (name_to_offset name))) binds)
    | ASeq(first, rest, _) -> max (helpC first) (helpA rest)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf(c, t, f, _) -> List.fold_left max 0 [helpI c; helpA t; helpA f]
    | CScIf(c, t, f, _) -> List.fold_left max 0 [helpI c; helpA t; helpA f]
    | CPrim1(_, i, _) -> helpI i
    | CPrim2(_, i1, i2, _) -> max (helpI i1) (helpI i2)
    | CApp(_, args, _, _) -> List.fold_left max 0 (List.map helpI args)
    | CTuple(vals, _) -> List.fold_left max 0 (List.map helpI vals)
    | CGetItem(t, _, _) -> helpI t
    | CSetItem(t, _, v, _) -> max (helpI t) (helpI v)
    | CLambda(args, body, _) ->
      let new_env = (List.mapi (fun i a -> (a, RegOffset(word_size * (i + 3), RBP))) args) @ env in
      deepest_stack body new_env
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNil _ -> 0
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmId(name, _) -> name_to_offset name
  and name_to_offset name =
    match (find env name) with
    | RegOffset(bytes, RBP) -> bytes / (-1 * word_size) (* negative because stack direction *)
    | _ -> 0
  in max (helpA e) 0 (* if only parameters are used, helpA might return a negative value *)
;;

(* IMPLEMENT EVERYTHING BELOW *)

(* This data type lets us keep track of how a binding was introduced.
   We'll use it to discard unnecessary Seq bindings, and to distinguish 
   letrec from let. Essentially, it accumulates just enough information 
   in our binding list to tell us how to reconstruct an appropriate aexpr. *)
type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program([], body, _) -> AProgram(helpA body, ())
    | _ -> raise (InternalCompilerError "Top-level declarations should have been desugared away")
  and helpC (e : tag expr) : (unit cexpr * unit anf_bind list) = 
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
    | ELet((BBlank _, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BSeq(exp_ans)] @ body_setup)
    | ELet((BName(bind, _, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet(bind, exp_ans)] @ body_setup)
    | ELet((BTuple(binds, _), exp, _)::rest, body, pos) ->
       raise (InternalCompilerError("Tuple bindings should have been desugared away"))
    | ESeq(e1, e2, _) ->
       let (e1_ans, e1_setup) = helpC e1 in
       let (e2_ans, e2_setup) = helpC e2 in
       (e2_ans, e1_setup @ [BSeq e1_ans] @ e2_setup)
    | EApp(func, args, ct, _) ->
       let (func_ans, func_setup) = helpI func in
       let (args_ans, args_setup) = List.split (List.map helpI args) in
       (CApp(func_ans, args_ans, ct, ()), func_setup @ (List.concat args_setup))
    | ETuple(args, _) ->
       let (args_ans, args_setup) = List.split (List.map helpI args) in
       (CTuple(args_ans, ()), List.concat args_setup)
    | EGetItem(tup, idx, _) ->
       let (tup_ans, tup_setup) = helpI tup in
       let (idx_ans, idx_setup) = helpI idx in
       (CGetItem(tup_ans, idx_ans, ()), tup_setup @ idx_setup)
    | ESetItem(tup, idx, newval, _) ->
       let (tup_ans, tup_setup) = helpI tup in
       let (idx_ans, idx_setup) = helpI idx in
       let (newval_ans, newval_setup) = helpI newval in
       (CSetItem(tup_ans, idx_ans, newval_ans, ()), tup_setup @ idx_setup @ newval_setup)
    | ELambda(binds, body, _) ->
       let args = List.map
                    (fun a ->
                      match a with
                      | BBlank(tag) -> sprintf "blank$%d" tag
                      | BName(name, _, _) -> name
                      | BTuple(_, _) -> raise (InternalCompilerError "desugaring failed: tuples cannot be ANFed in lambda args"))
                    binds
       in (CLambda(args, helpA body, ()), [])
    | ELetRec(bindings, body, pos) ->
      let (body_ans, body_setup) = helpC body in
      let (new_bindings, bindings_setups) =
        List.fold_left
          (fun (acc_bindings, acc_setups) (bind, exp, _) ->
               begin
               match bind with
               | BName(name, _, _) ->
                 let (exp_ans, exp_setup) = helpC exp in
                   ((name, exp_ans)::acc_bindings, exp_setup @ acc_setups)
               | _ -> raise (InternalCompilerError "ANF-ing failed, letrec must only have BName bindings")
               end)
           ([], [])
           bindings
      in (body_ans, bindings_setups @ [BLetRec(new_bindings)] @ body_setup)
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * unit anf_bind list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])
    | ENil _ -> (ImmNil(), [])
    | ESeq(e1, e2, _) ->
       let (e1_imm, e1_setup) = helpI e1 in
       let (e2_imm, e2_setup) = helpI e2 in
       (e2_imm, e1_setup @ e2_setup)
    | ETuple(args, tag) ->
       let tmp = sprintf "tuple_%d" tag in
       let (args_imm, args_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), (List.concat args_setup) @ [BLet(tmp, CTuple(args_imm, ()))])
    | EGetItem(tup, idx, tag) ->
       let tmp = sprintf "getitem_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       (ImmId(tmp, ()), tup_setup @ idx_setup @ [BLet(tmp, CGetItem(tup_imm, idx_imm, ()))])
    | ESetItem(tup, idx, newval, tag) ->
       let tmp = sprintf "setitem_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       let (newval_imm, newval_setup) = helpI newval in
       (ImmId(tmp, ()), tup_setup @ idx_setup @ newval_setup @ [BLet(tmp, CSetItem(tup_imm, idx_imm, newval_imm, ()))])
    | EPrim1(op, arg, tag) ->
       let tmp = sprintf "unary_%d" tag in
       let (arg_imm, arg_setup) = helpI arg in
       (ImmId(tmp, ()), arg_setup @ [BLet(tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
       let tmp = sprintf "binop_%d" tag in
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (ImmId(tmp, ()), left_setup @ right_setup @ [BLet(tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [BLet(tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EScIf(cond, _then, _else, tag) ->
       let tmp = sprintf "scif_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [BLet(tmp, CScIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(func, args, ct, tag) ->
      let tmp = sprintf "app_%d" tag in
      let (func_imm, func_setup) = helpI func in
      let (args_imm, args_setup) = List.split (List.map helpI args) in
      (ImmId(tmp, ()), func_setup @ (List.concat args_setup) @ [BLet(tmp, CApp(func_imm, args_imm, ct, ()))])
    | ELet([], body, _) -> helpI body
    | ELet((BBlank _, exp, _)::rest, body, pos) ->
       let (exp_imm, exp_setup) = helpI exp in (* MUST BE helpI, to avoid any missing final steps *)
       let (body_imm, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_imm, exp_setup @ body_setup)
    | ELambda(binds, body, tag) ->
       raise (NotYetImplemented("Finish this case8"))
       (* Hint: use BLet to bind the answer *)
    | ELet((BName(bind, _, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet(bind, exp_ans)] @ body_setup)
    | ELet((BTuple(binds, _), exp, _)::rest, body, pos) ->
       raise (InternalCompilerError("Tuple bindings should have been desugared away"))
    | ELetRec(binds, body, tag) ->
       raise (NotYetImplemented("Finish this case9"))
       (* Hint: use BLetRec for each of the binds, and BLet for the final answer *)
  and helpA e : unit aexpr = 
    let (ans, ans_setup) = helpC e in
    List.fold_right
      (fun bind body ->
        (* Here's where the anf_bind datatype becomes most useful:
             BSeq binds get dropped, and turned into ASeq aexprs.
             BLet binds get wrapped back into ALet aexprs.
             BLetRec binds get wrapped back into ALetRec aexprs.
           Syntactically it looks like we're just replacing Bwhatever with Awhatever,
           but that's exactly the information needed to know which aexpr to build. *)
        match bind with
        | BSeq(exp) -> ASeq(exp, body, ())
        | BLet(name, exp) -> ALet(name, exp, body, ())
        | BLetRec(names) -> ALetRec(names, body, ()))
      ans_setup (ACExpr ans)
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

(* Is the id in the env? *)
let rec id_in_env (id : string) (env : env_entry envt) : bool =
  match env with
  | [] -> false
  | (k, Id(_)) :: tail ->
      if id = k then true
      else id_in_env id tail
;;


(* Add a list of unique args to an env as Vars *)
let rec add_args_to_env (args : (string * sourcespan) list) (env : env_entry envt) : env_entry envt =
  (* fold direction doesn't matter since arg names are required to be unique *)
  List.fold_left
    (fun env_acc arg ->
      match arg with
      | (arg_name, loc) -> (arg_name, Id(loc)) :: env_acc)
    env
    args
;;


let rec bind_pairs (binds : sourcespan bind list) : (string * sourcespan) list =
  match binds with
  | [] -> []
  | BBlank(loc) :: tail -> bind_pairs tail
  | BName(sym,_,loc) :: tail -> (sym,loc) :: (bind_pairs tail)
  | BTuple(tup_binds,loc) :: tail -> (bind_pairs tup_binds) @ (bind_pairs tail)
;;


let rec bind_list_pairs (binds : sourcespan binding list) : (string * sourcespan) list =
  match binds with
  | [] -> []
  | (bind,_,_) :: tail -> (bind_pairs [bind]) @ (bind_list_pairs tail)
;;

let rec check_dups (binds : (string * sourcespan) list) : exn list =
  match binds with
  | [] -> []
  | (sym,loc) :: tail -> (check_duplicate_binds sym loc tail) @ (check_dups tail)
;;

let dup_binding_exns (binds : sourcespan binding list) : exn list =
  check_dups (bind_list_pairs binds)
;;

let dup_bind_exns (binds : sourcespan bind list) : exn list =
  check_dups (bind_pairs binds)
;;


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
  in
  match p with
  | Program(decls, body, fake_loc) ->
      let init_env = [("cinput",Id(fake_loc)); ("cequal",Id(fake_loc))] in
      (* gather all functions into the env *)
      (* TODO- check for duplicates within each group (but not between groups!) *)
      (* TODO- add back env checks for decls
      let (env, init_errs) = setup_env decls init_env in
      (* check decls *)
      let decl_errs =
        List.fold_left
          (fun (acc : (exn list)) decl -> ((wf_D decl env) @ acc))
          []
          decls in*)
      let (env, init_errs) = (init_env, []) in
      let decl_errs = [] in
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
                let new_arg_sym = gensym "tup$" in
                let new_body = ELet([(arg, EId(new_arg_sym,bloc), bloc)], body_acc, bloc) in
                let new_bind = BName(new_arg_sym,false,bloc) in
                (new_bind::args_acc, new_body)
            end)
          args ([], body) in
        DFun(fname, desugared_args, desugared_body, loc)
  in
  match p with
  | Program(decls, body, loc) ->
    let innerHelpD = fun decls -> List.map helpD decls in
    let desugared_decls = List.map innerHelpD decls in
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
      (* (Pretty sure) this splits up lists of bindings into nested lets here *)
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
    | ELet(bindings, body, loc) -> helpBindings bindings (helpE body)
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
    let innerHelpD = fun decls -> List.map helpD decls in
    let desugared_decls = List.map innerHelpD decls in
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
      let innerHelpD = fun decls -> List.map help_decl decls in
      let rw_decls = List.map innerHelpD decls in
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
      let innerHelpD = fun decls -> List.map help_decl decls in
      let rw_decls = List.map innerHelpD decls in
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
      let innerHelpD = fun decls -> List.map help_decl decls in
      let rw_decls = List.map innerHelpD decls in
      let rw_body = help_expr body in
      Program(rw_decls, rw_body, loc)
;;

(* Convert a function decl to a binding (lambda bound to name) *)
let decl_to_binding (decl : sourcespan decl) : sourcespan binding =
  match decl with
  | DFun(fname, fargs, fbody, floc) ->
    let bnd = BName(fname, false, floc) in
    let expr = ELambda(fargs, fbody, floc) in
    (bnd, expr, floc)
;;

(* Desugar single decl group into a let-rec expression, wrapping the body *)
let desugar_decl_group (body : sourcespan expr) (decls : sourcespan decl list) : sourcespan expr =
  match decls with
  | [] -> body
  | DFun(fname, fargs, fbody, floc)::rest ->
    (* Still operate on whole list, we just split to check there is 1+ decl and get some loc info *)
    let decls_as_bindings = List.map decl_to_binding decls in
    ELetRec(decls_as_bindings, body, floc)
;;

(* Desugar declaration groups into explicit let-rec bindings *)
let desugar_decl_groups_to_binds (p : sourcespan program) : sourcespan program =
  match p with
  | Program(decls, body, loc) ->
      let new_body = List.fold_left desugar_decl_group body decls in
      (* don't touch the body otherwise, just looking at decls *)
      Program([], new_body, loc)
;;

(* TODO- refactor so that desugar_decl_groups_to_binds is the first thing that happens in desugar, then rest of desugarings should throw error if they find any decls (simplifying them) *)

(* TODO- every phase after desugar should also have 0 decls,
add InternalCompilerErrors for this and note at bottom of file *)


(* Desugaring:
 * rewrite decl groups as bindings
 * convert print() calls to func applications
 * and/or rewrite
 * let bindings with tuple on the LHS
 * tuples as func args
 * add let binding for every func arg (to prevent tail-recursion overwrite)
 * sequence -> let bindings with "_"
*)
let desugar (p : sourcespan program) : sourcespan program =
  desugar_decl_groups_to_binds
  (desugar_sequences
  (desugar_and_or
  (desugar_args_as_let_binds
  (* "desugar_decl_arg_tups" comes before "desugar_let_bind_tups" to make sure we
   * don't unnecessarily duplicate the "tup" variable we use as a func arg during
   * the "desugar_decl_arg_tups" phase. *)
  (desugar_let_bind_tups
  (desugar_decl_arg_tups p)))))
;;

(* Find all local variables *)
let local_vars (e: 'a aexpr) : string list =
  let rec help_aexpr (expr : 'a aexpr) (seen : StringSet.t) : StringSet.t =
    match expr with
    | ASeq(lhs, rhs, _) -> StringSet.union (help_cexpr lhs seen) (help_aexpr rhs seen)
    | ALet(bnd_name, bnd_exp, body, _) ->
      (StringSet.add bnd_name (StringSet.union (help_cexpr bnd_exp seen) (help_aexpr body (StringSet.add bnd_name seen))))
    | ALetRec(binds, body, _) ->
      let names = List.map fst binds in
      let names_set = StringSet.of_list names in
      let seen_with_names = StringSet.union names_set seen in
      (* TODO- should I remove this name from the names used in help_cexpr? *)
      let new_free = List.fold_left (fun free_acc (name, expr) -> StringSet.union free_acc (help_cexpr expr seen_with_names)) StringSet.empty binds in
      let body_free = help_aexpr body seen_with_names in
      (StringSet.union (StringSet.union names_set new_free) body_free)
    | ACExpr(exp) -> help_cexpr exp seen
  and help_cexpr (expr : 'a cexpr) (seen : StringSet.t) : StringSet.t =
    match expr with
    | CIf(cond, thn, els, _) ->
      StringSet.union (StringSet.union (help_imm cond seen) (help_aexpr thn seen)) (help_aexpr els seen)
    | CScIf(fst, snd, thd, _) ->
      StringSet.union (StringSet.union (help_imm fst seen) (help_aexpr snd seen)) (help_aexpr thd seen)
    | CPrim1(_, exp, _) -> help_imm exp seen
    | CPrim2(_, lhs, rhs, _) -> StringSet.union (help_imm lhs seen) (help_imm rhs seen)
    | CApp(func, args, _, _) ->
      StringSet.union
        (help_imm func seen)
        (List.fold_left (fun free_acc arg -> StringSet.union free_acc (help_imm arg seen)) StringSet.empty args)
    | CImmExpr(exp) -> help_imm exp seen
    | CTuple(elems, _) -> List.fold_left (fun free_acc elem -> StringSet.union free_acc (help_imm elem seen)) StringSet.empty elems
    | CGetItem(tup, idx, _) -> StringSet.union (help_imm tup seen) (help_imm idx seen)
    | CSetItem(tup, idx, newval, _) -> StringSet.union (StringSet.union (help_imm tup seen) (help_imm tup seen)) (help_imm newval seen)
    | CLambda(args, body, _) ->
      let args_set = StringSet.of_list args in
      let seen_with_args = StringSet.union args_set seen in
      help_aexpr body seen_with_args
  and help_imm (expr : 'a immexpr) (seen : StringSet.t) : StringSet.t =
    match expr with
    | ImmNum _ -> StringSet.empty
    | ImmBool _ -> StringSet.empty
    | ImmId(name, _) -> StringSet.empty
    | ImmNil _ -> StringSet.empty
  in
  StringSet.elements (help_aexpr e StringSet.empty)
;;

(* Find all free variables *)
let free_vars (e: 'a aexpr) : string list =
  let rec help_aexpr (expr : 'a aexpr) (seen : StringSet.t) : StringSet.t =
    match expr with
    | ASeq(lhs, rhs, _) -> StringSet.union (help_cexpr lhs seen) (help_aexpr rhs seen)
    | ALet(bnd_name, bnd_exp, body, _) ->
      StringSet.union (help_cexpr bnd_exp seen) (help_aexpr body (StringSet.add bnd_name seen))
    | ALetRec(binds, body, _) ->
      let names = List.map fst binds in
      let names_set = StringSet.of_list names in
      let seen_with_names = StringSet.union names_set seen in
      let new_free = List.fold_left (fun free_acc (name, expr) -> StringSet.union free_acc (help_cexpr expr seen_with_names)) StringSet.empty binds in
      let body_free = help_aexpr body seen_with_names in
      StringSet.union new_free body_free
    | ACExpr(exp) -> help_cexpr exp seen
  and help_cexpr (expr : 'a cexpr) (seen : StringSet.t) : StringSet.t =
    match expr with
    | CIf(cond, thn, els, _) ->
      StringSet.union (StringSet.union (help_imm cond seen) (help_aexpr thn seen)) (help_aexpr els seen)
    | CScIf(fst, snd, thd, _) ->
      StringSet.union (StringSet.union (help_imm fst seen) (help_aexpr snd seen)) (help_aexpr thd seen)
    | CPrim1(_, exp, _) -> help_imm exp seen
    | CPrim2(_, lhs, rhs, _) -> StringSet.union (help_imm lhs seen) (help_imm rhs seen)
    | CApp(func, args, _, _) ->
      StringSet.union
        (help_imm func seen)
        (List.fold_left (fun free_acc arg -> StringSet.union free_acc (help_imm arg seen)) StringSet.empty args)
    | CImmExpr(exp) -> help_imm exp seen
    | CTuple(elems, _) -> List.fold_left (fun free_acc elem -> StringSet.union free_acc (help_imm elem seen)) StringSet.empty elems
    | CGetItem(tup, idx, _) -> StringSet.union (help_imm tup seen) (help_imm idx seen)
    | CSetItem(tup, idx, newval, _) -> StringSet.union (StringSet.union (help_imm tup seen) (help_imm tup seen)) (help_imm newval seen)
    | CLambda(args, body, _) ->
      let args_set = StringSet.of_list args in
      let seen_with_args = StringSet.union args_set seen in
      help_aexpr body seen_with_args
  and help_imm (expr : 'a immexpr) (seen : StringSet.t) : StringSet.t =
    match expr with
    | ImmNum _ -> StringSet.empty
    | ImmBool _ -> StringSet.empty
    | ImmId(name, _) -> if StringSet.mem name seen then StringSet.empty else StringSet.singleton name
    | ImmNil _ -> StringSet.empty
  in
  StringSet.elements (help_aexpr e StringSet.empty)
;;


(* ASSUMES that the program has been alpha-renamed and all names are unique *)
let naive_stack_allocation (prog: tag aprogram) : tag aprogram * arg envt =
  let rec help_aexpr (body : tag aexpr) (si : int) (env : arg envt) : arg envt * int =
    match body with
    | ASeq(cexp, aexp, _) -> raise (NotYetImplemented "ASeq stack allocation not yet implemented")
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
    | CLambda(args, body, tag) ->
        let args_with_idx = List.mapi (fun i arg -> (arg, RegOffset((i + 3)*word_size, RBP))) args in
        let new_env = List.fold_left (fun accum_env cell -> cell :: accum_env) env args_with_idx in
        let self_name = sprintf "closure$%d" tag in
        let new_env_with_self = (self_name, RegOffset(2*word_size, RBP)) :: new_env in
        help_aexpr body si new_env_with_self
  in
  match prog with
  | AProgram(body, _) ->
      let (prog_env, _) = help_aexpr body 1 [] in
      (prog, prog_env)
;;


(* Compiled Type Checking *)
let check_rax_for_num (err_lbl : string) : instruction list =
  [
   (* This "test" trick depends on num_tag being 0. R8 used because Test doesn't support imm64 *)
   ILineComment("check_rax_for_num (" ^ err_lbl ^ ")");
   IMov(Reg(R8), HexConst(num_tag_mask));
   ITest(Reg(RAX), Reg(R8));
   IJnz(Label(err_lbl));
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
   IJnz(Label(err_lbl));
  ]

let check_for_overflow = [IJo(Label("err_OVERFLOW"))]


let check_rax_for_tup (err_lbl : string) : instruction list =
  [
   (* Operate on temp register R8 instead of RAX. This is because we call AND
    * on the register, which will alter the value. We want to preserve the value
    * in RAX, hence we operate on R8 instead. R9 is used as intermediate because
      And, Cmp don't work on imm64s *)
   ILineComment("check_rax_for_tup (" ^ err_lbl ^ ")");
   IMov(Reg(R8), Reg(RAX));
   IMov(Reg(R9), HexConst(tuple_tag_mask));
   IAnd(Reg(R8), Reg(R9));
   IMov(Reg(R9), HexConst(tuple_tag));
   ICmp(Reg(R8), Reg(R9));
   IJne(Label(err_lbl));
  ]

let check_rax_for_nil (err_lbl : string) : instruction list =
  [
   ILineComment("check_rax_for_nil (" ^ err_lbl ^ ")");
   IMov(Reg(R8), const_nil);
   ICmp(Reg(RAX), Reg(R8));
   IJe(Label(err_lbl));
  ]


(* RAX should be the snakeval of the index (in a tuple)*)
(* DO NOT MODIFY RAX *)
let check_rax_for_tup_smaller (err_lbl : string) : instruction list =
  [
   ILineComment("check_rax_for_tup_smaller (" ^ err_lbl ^ ")");
   ICmp(Reg(RAX), Const(0L));
   (* no temp register because imm32 0 will be "sign-extended to imm64", which should still be 0 *)
   IJl(Label(err_lbl));
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
   IJge(Label(err_lbl));
  ]


let compile_fun_prelude (fun_name : string) (args : string list) (env : arg envt) (num_local_vars : int): instruction list =
  [
    ILabel(fun_name);
    IPush(Reg(RBP));
    IMov(Reg(RBP), Reg(RSP));

  ]

let compile_fun_postlude (num_local_vars : int) : instruction list =
  [
    IMov(Reg(RSP), Reg(RBP));  (* Move stack to how it was at start of this function *)
    IPop(Reg(RBP));
    IRet;
  ]


let rec update_env_for_closure (free_vars_with_idx : (int * string) list) (env : arg envt) : (arg envt) =
  match env with
  | [] -> []
  | fst :: rest ->
    let new_env_var = (update_env_var_for_closure fst free_vars_with_idx) in
    new_env_var :: (update_env_for_closure free_vars_with_idx rest)
and update_env_var_for_closure (env_var : string * arg) (free_vars_with_idx : (int * string) list) : string * arg =
  match free_vars_with_idx with
  | [] -> env_var
  | (fvidx, fvname) :: rest ->
    if fvname = fst env_var
    then (fvname, Sized(QWORD_PTR, RegOffset(~-1 * (1 + fvidx) * word_size, RBP)))
    else update_env_var_for_closure env_var rest
;;


let rec push_free_vars_from_closure (cur_idx : int) (num_free_vars : int): instruction list =
  if cur_idx >= (num_free_vars)
  then []
  else IPush(Sized(QWORD_PTR, RegOffset((3 + cur_idx) * word_size, RAX))) :: (push_free_vars_from_closure (cur_idx + 1) num_free_vars)


let rec compile_aexpr (e : tag aexpr) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  match e with
  | ALet(id, bind, body, _) ->
    let compiled_bind = compile_cexpr bind env num_args false in
    let dest = (find env id) in
    let compiled_body = compile_aexpr body env num_args is_tail in
    [ILineComment(sprintf "Let_%s" id)]
    @ compiled_bind
    @ [IMov(dest, Reg(RAX))]
    @ compiled_body
  | ACExpr(expr) -> (compile_cexpr expr env num_args is_tail)
  | ASeq(left, right, tag) ->
    let seq_left_txt = sprintf "seq_left_%d" tag in
    let seq_right_txt = sprintf "seq_right_%d" tag in
    let compiled_left = (compile_cexpr left env num_args is_tail) in
    let compiled_right = (compile_aexpr right env num_args is_tail) in
    [ILineComment(seq_left_txt)]
    @ compiled_left
    @ [ILineComment(seq_right_txt)]
    @ compiled_right
  | ALetRec(bindings, body, tag) ->
    (* TODO fix the 0 and false, they are placeholders for now but used for tailcall optimization *)
    let compiled_bindings =
      List.fold_left (fun cb_acc (name, bound_body) ->
                       let dest = (find env name) in
                         (compile_cexpr bound_body env 0 false) @ [IMov(dest, Reg(RAX))] @ cb_acc)
                       []
                       bindings in
    [ILineComment(sprintf "LetRec$%d" tag)]
    @ compiled_bindings
    @ (compile_aexpr body env 0 false)
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
     @ [IJz(Label(lbl_els))]

     @ [ILabel(lbl_thn)]
     @ (compile_aexpr thn env num_args is_tail)
     @ [IJmp(Label(lbl_done))]

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
     @ [IJz(Label(lbl_els))]

     @ [ILabel(lbl_thn)]
     (* LHS is compiled before RHS, so definitely not tail position *)
     @ (compile_aexpr thn env num_args false)
     @ [IJmp(Label(lbl_done))]

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
        | Print -> [IMov(Reg(RDI), body_imm); ICall(Label("print"));]
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
           IJz(Label(true_lbl));
           (* case not bool *)
           ILabel(false_lbl);
           IMov(Reg(RAX), const_false);
           IJmp(Label(done_lbl));
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
           IJz(Label(true_lbl));
           (* case not num *)
           ILabel(false_lbl);
           IMov(Reg(RAX), const_false);
           IJmp(Label(done_lbl));
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
            (* TODO Lerner provided this *)
            raise (NotYetImplemented "PrintStack not yet implemented")
        | IsTuple ->
          let true_lbl = sprintf "is_tup_true_%d" tag in
          let false_lbl = sprintf "is_tup_false_%d" tag in
          let done_lbl = sprintf "is_tup_done_%d" tag in
          [
           IMov(Reg(RAX), body_imm);
           (* Don't need to save RAX on the stack because we overwrite the
            * value with true/false later. R8 used because And, Cmp don't support imm64 *)
           IMov(Reg(R8), HexConst(tuple_tag_mask));
           IAnd(Reg(RAX), Reg(R8));
           IMov(Reg(R8), HexConst(tuple_tag));
           ICmp(Reg(RAX), Reg(R8));
           IJz(Label(true_lbl));
           (* case not tup *)
           ILabel(false_lbl);
           IMov(Reg(RAX), const_false);
           IJmp(Label(done_lbl));
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
         @ [IJg(Label(lbl_done))]

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
         @ [IJge(Label(lbl_done))]

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
         @ [IJl(Label(lbl_done))]

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
         @ [IJle(Label(lbl_done))]

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
         @ [IJe(Label(lbl_done))]

         @ [ILabel(lbl_false)]
         @ [IMov(Reg(RAX), const_false)]

         @ [ILabel(lbl_done)]
     end
  | CLambda(params, body, tag) ->
    let arity = List.length params in
    let closure_lbl = sprintf "closure$%d" tag in
    let closure_done_lbl = sprintf "closure_done$%d" tag in
    let num_body_vars = (deepest_stack body env) in
    let free_vars_list = List.sort String.compare (free_vars (ACExpr(e))) in
    let num_free_vars = List.length free_vars_list in
    let add_free_vars_to_closure =
      List.flatten (List.mapi (fun idx fv ->
                 [
                 IMov(Reg(scratch_reg), (find env fv));
                 IMov(Sized(QWORD_PTR, RegOffset((3 + idx)*word_size, heap_reg)), Reg(scratch_reg));
                 ])
                free_vars_list) in
    let local_vs_list = List.sort String.compare (local_vars (ACExpr(e))) in
    let free_vars_with_idx = List.mapi (fun idx fv -> (idx, fv)) (free_vars_list@local_vs_list) in
    let new_env = update_env_for_closure free_vars_with_idx env in
    let prelude = compile_fun_prelude closure_lbl params new_env num_body_vars in
    let compiled_body = compile_aexpr body new_env (List.length params) true in
    let postlude = compile_fun_postlude num_body_vars in
    let true_heap_size = 3 + num_free_vars in
    let reserved_heap_size = true_heap_size + (true_heap_size mod 2) in
    [IJmp(Label(closure_done_lbl))]
(*    @ [ILineComment(sprintf "numlocals%d" (List.length local_vs_list))]*)
    @ prelude
    @ [IMov(Reg(RAX), RegOffset(2*word_size, RBP))]
    (* Now RAX has the (tagged) func value *)
    @ [
       ISub(Reg(RAX), HexConst(closure_tag)); (* now RAX is heap addr to closure *)
      ]
    @ (push_free_vars_from_closure 0 num_free_vars)
    @ [    (* Don't use temp register here because we assume the RHS will never be very big *)
    ISub(Reg(RSP), Const(Int64.of_int (word_size * num_body_vars)))  (* allocates stack space for all local vars *)]
    @ compiled_body
    @ postlude
    @ [
      ILabel(closure_done_lbl);
      IMov(Sized(QWORD_PTR, RegOffset(0*word_size, heap_reg)), Const(Int64.of_int arity));
      IMov(Sized(QWORD_PTR, RegOffset(1*word_size, heap_reg)), Label(closure_lbl));
      IMov(Sized(QWORD_PTR, RegOffset(2*word_size, heap_reg)), Const(Int64.of_int num_free_vars));
      ]
    @ add_free_vars_to_closure
    @ [
      IMov(Reg(RAX), Reg(heap_reg));
      IAdd(Reg(RAX), HexConst(closure_tag));
      IAdd(Reg(heap_reg), Const(Int64.of_int (reserved_heap_size*word_size)));
      ]
  | CApp(func, args, ct, tag) ->
    let f_num_args = (List.length args) in
    let is_even_f_num_args = (f_num_args + 1) mod 2 == 0 in
    let padding = (if is_even_f_num_args then [] else [IMov(Reg(R8), HexConst(0xF0F0F0F0L)); IPush(Reg(R8))]) in
    (* Push the args onto stack in reverse order *)
    let args_rev = List.rev args in
    let f_num_args_passed = f_num_args + (if is_even_f_num_args then 0 else 1) in
    let is_even_num_args = num_args mod 2 == 0 in
    let num_args_passed = num_args + (if is_even_num_args then 0 else 1) in
    (* Technically we allow tailcall optimization with 1 more arg if this function has odd num of args *)
    let compiled_func = compile_imm func env in
    begin match ct with
    (*| Native ->
        if f_num_args > 6 then
          raise (InternalCompilerError "Our compiler does not support native calls with more than 6 arg")
        else
          let move_args_to_input_registers =
            List.mapi
             (fun idx arg ->
               let reg = List.nth first_six_args_registers idx in
               let compiled_imm = (compile_imm arg env) in
                 IMov(Reg(reg), compiled_imm))
             args
          in
          begin
          match func with
          | ImmId(fname, _) -> move_args_to_input_registers @ [ICall(Label(fname))]
          | _ -> raise (InternalCompilerError "TODO add errors here")
          end*)
    | Snake ->
        (*TODO- have this actually check if is_tail and fix that case *)
        if false && (f_num_args <= num_args_passed) then
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
            let body_label = sprintf "closure_body$%d" tag in
            compiled_args @ [IJmp(Label(body_label))]
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
            let closure_check =
            [ILineComment("check_rax_for_closure (err_CALL_NOT_CLOSURE)");
             (*IMov(Reg(R8), Reg(RAX));*)
             IMov(Reg(R9), HexConst(closure_tag_mask));
             IAnd(Reg(RAX), Reg(R9));
             IMov(Reg(R9), HexConst(closure_tag));
             ICmp(Reg(RAX), Reg(R9));
             IJne(Label("err_CALL_NOT_CLOSURE"));] in
            let check_closure_for_arity =
            [ILineComment("check_closure_for_arity (err_CALL_ARITY_ERR)");
             (* RAX is tagged ptr to closure on heap *)
             IMov(Reg(RAX), compiled_func);
             ISub(Reg(RAX), HexConst(closure_tag)); (* now RAX is heap addr to closure *)
             IMov(Reg(RAX), RegOffset(0,RAX)); (* get the arity (machine int) *)
             ICmp(Reg(RAX), Const(Int64.of_int f_num_args)); (* no temp reg, assume won't have that many args *)
             IJne(Label("err_CALL_ARITY_ERR"));] in
            let padded_comp_args = padding @ compiled_args in
            [IMov(Reg(RAX), compiled_func);]
            @ closure_check
            @ check_closure_for_arity
            @ padded_comp_args
            @ [
              IMov(Reg(RAX), compiled_func);
              IPush(Reg(RAX)); (*Push the tagged func itself onto the stack*)
              ISub(Reg(RAX), HexConst(closure_tag)); (* now RAX is heap addr to closure *)
              IMov(Reg(RAX), RegOffset(1*word_size,RAX)); (* get the code ptr (machine addr) *)
              ICall(Reg(RAX));
              (* Don't use temp register here because we assume the RHS will never be very big *)
              IAdd(Reg(RSP), Const(Int64.of_int (word_size * (f_num_args_passed + 1))));
              (* add 1 because we pushed the func value itself *)
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


let compile_prog ((anfed : tag aprogram), (env : arg envt)) : string =
  match anfed with
  | AProgram(body, _) ->
      let heap_start = [
          ILineComment("heap start");
          IInstrComment(IMov(Reg(heap_reg), Reg(List.nth first_six_args_registers 0)), "Load heap_reg with our argument, the heap pointer");
          IInstrComment(IAdd(Reg(heap_reg), Const(15L)), "Align it to the nearest multiple of 16");
          IInstrComment(IAnd(Reg(heap_reg), HexConst(0xFFFFFFFFFFFFFFF0L)), "by adding no more than 15 to it")
        ] in
      let num_prog_body_vars = (deepest_stack body env) in
      let compiled_body = (compile_aexpr body env 0 false) in
      let prelude =
        "section .text
extern error
extern print
extern cinput
extern cequal
global our_code_starts_here" in
      let stack_setup = (compile_fun_prelude "our_code_starts_here" [] env num_prog_body_vars) in
      let postlude =
      [ILabel("program_done");]
      @ compile_fun_postlude num_prog_body_vars
      @ [ (* Error Labels *)
          ILabel("err_COMP_NOT_NUM");
          IMov(Reg(RDI), Const(err_COMP_NOT_NUM));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_ARITH_NOT_NUM");
          IMov(Reg(RDI), Const(err_ARITH_NOT_NUM));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_LOGIC_NOT_BOOL");
          IMov(Reg(RDI), Const(err_LOGIC_NOT_BOOL));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_IF_NOT_BOOL");
          IMov(Reg(RDI), Const(err_IF_NOT_BOOL));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_OVERFLOW");
          IMov(Reg(RDI), Const(err_OVERFLOW));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_GET_NOT_TUPLE");
          IMov(Reg(RDI), Const(err_GET_NOT_TUPLE));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_GET_LOW_INDEX");
          IMov(Reg(RDI), Const(err_GET_LOW_INDEX));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_GET_HIGH_INDEX");
          IMov(Reg(RDI), Const(err_GET_HIGH_INDEX));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_GET_NOT_NUM");
          IMov(Reg(RDI), Const(err_GET_NOT_NUM));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_NIL_DEREF");
          IMov(Reg(RDI), Const(err_NIL_DEREF));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_OUT_OF_MEMORY");
          IMov(Reg(RDI), Const(err_OUT_OF_MEMORY));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_SET_NOT_TUPLE");
          IMov(Reg(RDI), Const(err_SET_NOT_TUPLE));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_SET_LOW_INDEX");
          IMov(Reg(RDI), Const(err_SET_LOW_INDEX));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_SET_NOT_NUM");
          IMov(Reg(RDI), Const(err_SET_NOT_NUM));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_SET_HIGH_INDEX");
          IMov(Reg(RDI), Const(err_SET_HIGH_INDEX));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_CALL_NOT_CLOSURE");
          IMov(Reg(RDI), Const(err_CALL_NOT_CLOSURE));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_CALL_ARITY_ERR");
          IMov(Reg(RDI), Const(err_CALL_ARITY_ERR));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_BAD_INPUT");
          IMov(Reg(RDI), Const(err_BAD_INPUT));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_TUP_IDX_NOT_NUM");
          IMov(Reg(RDI), Const(err_TUP_IDX_NOT_NUM));
          ICall(Label("error"));
          IJmp(Label("program_done"));
        ] in
      let body_assembly_string =
      (to_asm (stack_setup @
      [(* Don't use temp register here because we assume the RHS will never be very big *)
       ISub(Reg(RSP), Const(Int64.of_int (word_size * num_prog_body_vars)))  (* allocates stack space for all local vars *)]
      @ heap_start @ compiled_body @ postlude)) in
      sprintf "%s%s\n" prelude body_assembly_string


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
