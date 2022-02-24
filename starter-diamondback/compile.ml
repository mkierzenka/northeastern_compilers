open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
       
type 'a envt = (string * 'a) list

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
;;

let const_true    = HexConst(0xFFFFFFFFFFFFFFFFL)
let const_false   = HexConst(0x7FFFFFFFFFFFFFFFL)
let bool_mask     = HexConst(0x8000000000000000L)
let bool_tag      = 0x0000000000000007L
let bool_tag_mask = 0x0000000000000007L
let num_tag       = 0x0000000000000000L
let num_tag_mask  = 0x0000000000000001L

let err_COMP_NOT_NUM   = 1L
let err_ARITH_NOT_NUM  = 2L
let err_LOGIC_NOT_BOOL = 3L
let err_IF_NOT_BOOL    = 4L
let err_OVERFLOW       = 5L

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]


(* You may find some of these helpers useful *)
let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y,v)::rest ->
     if y = x then v else find rest x

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
    | CApp(_, args, _) -> List.fold_left max 0 (List.map helpI args)
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmId(name, _) -> name_to_offset name
  and name_to_offset name =
    match (find env name) with
    | RegOffset(bytes, RBP) -> bytes / (-1 * word_size)  (* negative because stack direction *)
    | _ -> 0
  in max (helpA e) 0 (* if only parameters are used, helpA might return a negative value *)
;;

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

(* IMPLEMENT EVERYTHING BELOW *)

let rec lookup_rename (x : string) (env : (string * string) list) : string =
  match env with
  | [] -> failwith (sprintf "Failed to lookup %s" x) (* should never happen, make sure to check_scope and tag first *)
  | (k, v) :: tail ->
      if k = x
      then v
      else lookup_rename x tail
;;

let rename (e : tag program) : tag program =
  let rec help_decl (decls : tag decl list) : tag decl list =
    match decls with
    | [] -> []
    | DFun(fname, args, body, tag) :: tail ->
        (* TODO do we need to pass in the params in the env?? *)
        let newbody = help_expr [] body in
        DFun(fname, args, newbody, tag) :: (help_decl tail)
  and help_expr (env : (string * string) list) (e : tag expr) : tag expr =
    match e with
    | EId(x, tag) -> EId((lookup_rename x env), tag)
    | ELet(binds, body, tag) ->
        let (newbinds, newenv) = bind_help env binds in
        let newbody = help_expr newenv body in
        ELet(newbinds, newbody, tag)
    | ENumber(n, tag) -> e
    | EBool(b, tag) -> e
    | EPrim1(op, e, t) -> EPrim1(op, (help_expr env e), t)
    | EPrim2(op, e1, e2, t) -> EPrim2(op, (help_expr env e1), (help_expr env e2), t)
    | EIf(cond, thn, els, t) -> EIf((help_expr env cond), (help_expr env thn), (help_expr env els), t)
    (* TODO add this back *)
    (*| EScIf(cond, thn, els, t) -> EScIf((help_expr env cond), (help_expr env thn), (help_expr env els), t)*)
    | EApp(fname, args, t) -> e
  and bind_help (env : (string * string) list) (binds : tag bind list) : tag bind list * ((string * string) list) =
    match binds with
    | [] -> (binds, env)
    | (sym, expr, t) :: tail ->
        let newexpr = help_expr env expr in
        let newsym = sprintf "%s#%d" sym t in
        let (newbinds, newenv) = bind_help ((sym, newsym) :: env) tail in
        ((newsym, newexpr, t) :: newbinds, newenv)
  in
  match e with
  | Program(decls, expr, tag) ->
      let newdecls = help_decl decls in
      let newbody = help_expr [] expr in
      Program(newdecls, newbody, tag)
;;



let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program(decls, body, _) -> AProgram(List.map helpD decls, helpA body, ())
  and helpD (d : tag decl) : unit adecl =
    match d with
    | DFun(name, args, body, _) -> ADFun(name, List.map fst args, helpA body, ())
  and helpArgs (args : tag expr list) : (unit immexpr list * (string * unit cexpr) list) =
    match args with
    | [] -> ([], [])
    | expr :: tail ->
      let (immedsTail, setupsTail) = (helpArgs tail) in
      let (immedExpr, setupExpr) = (helpI expr) in
      (immedExpr :: immedsTail, setupExpr @ setupsTail)
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
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    | EApp(funname, args, _) ->
       let (immargs, args_setups) = (helpArgs args) in
       (CApp(funname, immargs, ()), args_setups)
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * (string * unit cexpr) list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])

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
    | EApp(funname, args, tag) ->
       let tmp = sprintf "app_%d" tag in
       let (capp, capp_setup) = helpC e in
       (ImmId(tmp, ()), capp_setup @ [(tmp, capp)])
    | ELet([], body, _) -> helpI body
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
  and helpA e : unit aexpr = 
    let (ans, ans_setup) = helpC e in
    List.fold_right (fun (bind, exp) body -> ALet(bind, exp, body, ())) ans_setup (ACExpr ans)
  in
  helpP p
;;


(* TODO possibly move typedef to exprs? *)
type id_t =
  | Var
  | Func of int
;;

type env_entry = sourcespan * id_t
;;


(* Given a function name and a list of decls, this function will check whether the function name
 * is duplicated in the decl list.  If it is, then we will return a list that contains the
 * DuplicateFun error. *)
let rec check_duplicate_decl (fname : string) (decls : sourcespan decl list) (existing : sourcespan) : exn list =
  match decls with
  | [] -> [] (* no duplicates found -> no error *)
  | DFun(k, _, _, loc) :: tail ->
      if k = fname then
        [DuplicateFun(fname, loc, existing)]
      else
        check_duplicate_decl fname tail loc
;;

let rec check_duplicate_var (sym : string) (binds : sourcespan bind list) (existing : sourcespan) : exn list =
  match binds with
  | [] -> [] (* no duplicates found -> no error *)
  | (k, v, loc) :: tail ->
      if k = sym then
        [DuplicateId(sym, loc, existing)]
      else
        check_duplicate_var sym tail loc
;;

let rec var_in_env (id : string) (env : env_entry envt) : bool =
  match env with
  | [] -> false
  | (k, (_, Var)) :: tail ->
      if id = k then true
      else var_in_env id tail
  | (k, (_, Func(_))) :: tail ->
      (* an optimization: funcs are last in our env so by the time we see
       * the first func we know we can stop looking for a var *)
      false
;;

let rec func_in_env (id : string) (env : env_entry envt) : bool =
  match env with
  | [] -> false
  | (k, (_, Var)) :: tail ->
      (* this key semantic choice stipulates that variables shadow functions *)
      if id = k then false
      else func_in_env id tail
  | (k, (_, Func(_))) :: tail ->
      if id = k then true
      else func_in_env id tail
;;

let rec add_args_to_env (args : (string * sourcespan) list) (env : env_entry envt) : env_entry envt =
  (* fold direction doesn't matter since arg names are required to be unique *)
  List.fold_left
    (fun env_acc arg ->
      match arg with
      | (arg_name, loc) -> (arg_name, (loc, Var)) :: env_acc)
    env
    args
;;

let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  (* Goes through the list of function decls and adds them all to our env.  We also
   * gather any errors along the way. *)
  let rec setup_env (d : sourcespan decl list) : (env_entry envt) * (exn list) =
    match d with
    | [] -> ([], [])
    | DFun(fname, args, body, loc) :: tail ->
        let (tail_env, tail_errs) = (setup_env tail) in
        let new_errs = (check_duplicate_decl fname tail loc) @ tail_errs in
        let new_env = (fname, (loc, Func(List.length args))) :: tail_env in
        (new_env, new_errs)
  (* checks an expr to see if it's well formed *)
  and wf_E (e : sourcespan expr) (env : env_entry envt) : (exn list) =
    match e with
    | ELet(binds, body, loc) ->
        let (let_env, let_errs) = wf_Binds binds env in
        let_errs @ (wf_E body let_env)
    | EPrim1(op, expr, _) -> wf_E expr env
    | EPrim2(op, lhs, rhs, _) -> (wf_E lhs env) @ (wf_E rhs env)
    | EIf(cond, thn, els, _) -> (wf_E cond env) @ (wf_E thn env) @ (wf_E els env)
    | ENumber(n, loc) ->
       if n > (Int64.div Int64.max_int 2L) || n < (Int64.div Int64.min_int 2L) then
         [Overflow(n, loc)]
       else
         []
    | EBool _ -> []
    | EId(id, loc) ->
        if var_in_env id env then []
        else [UnboundId(id, loc)]
    | EApp(fname, args, loc) ->
        let arg_errs = List.fold_left (fun errs arg -> errs @ (wf_E arg env)) [] args in
        if func_in_env fname env then
          let (decl_loc, id_t) = find env fname in
          match id_t with
          | Func(arity) ->
              let callsite_arity = List.length args in
              if arity = callsite_arity then
                arg_errs
              else
                [Arity(arity,callsite_arity,loc)] @ arg_errs
          | Var -> raise (InternalCompilerError (sprintf "Applying variable %s as a function" fname))
        else
          [UnboundFun(fname,loc)] @ arg_errs
  and wf_Binds (binds : sourcespan bind list) (env : env_entry envt) : (env_entry envt) * (exn list) =
    match binds with
    | [] -> (env, [])
    | (sym, expr, loc) :: tail ->
        let (tail_env, tail_errs) = wf_Binds tail env in
        let new_env = (sym, (loc, Var)) :: env in
        (new_env, (check_duplicate_var sym tail loc) @ tail_errs)
  (* checks a decl list to see if it's well formed *)
  and wf_D (d : sourcespan decl list) (env : env_entry envt) : (exn list) =
    match d with
    | [] -> []
    | DFun(fname, args, body, _) :: tail ->
        wf_E body (add_args_to_env args env)
  in
  match p with
  | Program(decls, body, _) ->
      (* gather all functions into the env *)
      let (env, init_errs) = setup_env decls in
      (* check decls *)
      let decl_errs = wf_D decls env in
      (* check the body *)
      let body_errs = wf_E body env in
      if (init_errs = []) && (decl_errs = []) && (body_errs = []) then
        Ok(p)
      else
        Error(init_errs @ decl_errs @ body_errs)
;;

(* ASSUMES that the program has been alpha-renamed and all names are unique *)
let naive_stack_allocation (prog : tag aprogram) : tag aprogram * arg envt =
  raise (NotYetImplemented "Extract your stack-slot allocation logic from Cobra's compile_expr into here")
(* In Cobra, you had logic somewhere that tracked the stack index, starting at 1 and incrementing it
   within the bodies of let-bindings.  It built up an environment that mapped each let-bound name to
   a stack index, so that RegOffset(~-8 * stackIndex, RBP) stored the value of that let-binding.
   In this function, you should build up that environment, and return a pair of the already-ANF'ed 
   program and that environment, which can then both be passed along to compile_prog to finish compilation.

   Since this environment-building step comes *after* renaming, you may rely on the invariant that every
   name in the program appears bound exactly once, and therefore those names can be used as keys in 
   an environment without worry of shadowing errors.
*)
;;

let rec compile_fun (fun_name : string) (args : string list) (env : arg envt) : instruction list =
  raise (NotYetImplemented "Compile funs not yet implemented")
and compile_aexpr (e : tag aexpr) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  raise (NotYetImplemented "Compile aexpr not yet implemented")
and compile_cexpr (e : tag cexpr) (env : arg envt) (num_args : int) (is_tail : bool) =
  raise (NotYetImplemented "Compile cexpr not yet implemented")
and compile_imm e (env : arg envt) =
  match e with
  | ImmNum(n, _) -> Const(Int64.shift_left n 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)

let compile_decl (d : tag adecl) (env : arg envt): instruction list =
  raise (NotYetImplemented "Compile decl not yet implemented")

let compile_prog ((anfed : tag aprogram), (env : arg envt)) : string =
  raise (NotYetImplemented "Compiling programs not implemented yet")

(* Feel free to add additional phases to your pipeline.
   The final pipeline phase needs to return a string,
   but everything else is up to you. *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase locate_bindings naive_stack_allocation)
  |> (add_phase result compile_prog)
;;
