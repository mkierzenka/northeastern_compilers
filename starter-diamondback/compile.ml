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
  | EScIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
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
    | CScIf(c, t, f, _) -> List.fold_left max 0 [helpI c; helpA t; helpA f]
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

let and_or_rewrite (p : 'a program) : unit program =
  let rec help_decl (d : 'a decl) : unit decl =
    match d with
    | DFun(fname, args, body, _) ->
        let rw_body = help_expr body in
        let rw_args =
          List.map
            (fun arg ->
              match arg with
              | (sym, _) -> (sym, ()))
            args in
        DFun(fname, rw_args, rw_body, ())
  and help_expr (e : 'a expr) : unit expr =
    match e with
    | EPrim2(op, lhs, rhs, _) ->
       let lhs_untagged = help_expr lhs in
       let rhs_untagged = help_expr rhs in
       begin match op with
        (* (e1 && e2) -> (if !e1: false else: e2) *)
        | And -> EScIf(EPrim1(Not, lhs_untagged, ()), EBool(false, ()), rhs_untagged, ())
        (* (e1 || e2) -> (if e1: true else: e2) *)
        | Or -> EScIf(lhs_untagged, EBool(true, ()), rhs_untagged, ())
        | _ -> EPrim2(op, (help_expr lhs), (help_expr rhs), ())
       end
    | ELet(binds, body, _) -> ELet((bind_helper binds), (help_expr body), ())
    | EPrim1(op, expr, _) -> EPrim1(op, (help_expr expr), ())
    | EIf(cond, thn, els, _) ->
        EIf((help_expr cond), (help_expr thn), (help_expr els), ())
    | ENumber(n, _) -> ENumber(n, ())
    | EBool(b, _) -> EBool(b, ())
    | EId(sym, _) -> EId(sym, ())
    | EScIf _ -> raise (InternalCompilerError "Impossible: 'EScIf' is not in syntax")
    | EApp(fname, args, _) ->
        let rw_args = List.map help_expr args in
        EApp(fname, rw_args, ())
  and bind_helper (binds : 'a bind list) : unit bind list =
    match binds with
    | [] -> []
    | (sym, v, _) :: tail -> (sym, (help_expr v), ()) :: (bind_helper tail)
  in
  match p with
  | Program(decls, body, _) ->
      let rw_decls = List.map help_decl decls in
      let rw_body = help_expr body in
      Program(rw_decls, rw_body, ())
;;

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
        (* Note, we do not rename func args to include tags, since no nested function decls so no name conflicts *)
        let args_env = (List.map
                        (fun tagged_arg -> let arg_name = (fst tagged_arg) in (arg_name, arg_name))
                        args) in
        let newbody = help_expr args_env body in
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
    | EScIf(cond, thn, els, t) -> EScIf((help_expr env cond), (help_expr env thn), (help_expr env els), t)
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
    | EScIf(cond, _then, _else, _) ->
       let (cond_imm, cond_setup) = helpI cond in
       (CScIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
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
    | EScIf(cond, _then, _else, tag) ->
       let tmp = sprintf "if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [(tmp, CScIf(cond_imm, helpA _then, helpA _else, ()))])
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
type env_entry =
  | Var
  | Func of int
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

(* TODO better comment *)
(* for lets *)
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
  | (k, Var) :: tail ->
      if id = k then true
      else var_in_env id tail
  | (k, Func(_)) :: tail ->
      (* an optimization: funcs are last in our env so by the time we see
       * the first func we know we can stop looking for a var *)
      false
;;

let rec func_in_env (id : string) (env : env_entry envt) : bool =
  match env with
  | [] -> false
  | (k, Var) :: tail ->
      (* this key semantic choice stipulates that variables shadow functions *)
      if id = k then false
      else func_in_env id tail
  | (k, Func(_)) :: tail ->
      if id = k then true
      else func_in_env id tail
;;

let rec add_args_to_env (args : (string * sourcespan) list) (env : env_entry envt) : env_entry envt =
  (* fold direction doesn't matter since arg names are required to be unique *)
  List.fold_left
    (fun env_acc arg ->
      match arg with
      | (arg_name, loc) -> (arg_name, Var) :: env_acc)
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
        let new_env = (fname, Func(List.length args)) :: tail_env in
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
    | EScIf(cond, thn, els, _) -> raise (InternalCompilerError "EScIf is not part of the diamondback language")
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
          let id_t = find env fname in
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
        let new_env = (sym, Var) :: tail_env in
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
  in
  match prog with
  | AProgram(decls, body, _) ->
      let decl_env =
        List.fold_left (fun accum_env decl -> help_decl decl accum_env) [] decls in
      let (prog_env, _) = help_aexpr body 1 decl_env in
      (prog, prog_env)

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


let compile_fun_prelude (fun_name : string) (args : string list) (env : arg envt) (num_local_vars : int): instruction list =
  [
    ILabel(fun_name);
    IPush(Reg(RBP));
    IMov(Reg(RBP), Reg(RSP));
    ISub(Reg(RSP), Const(Int64.of_int (word_size * num_local_vars)))  (* allocates stack space for all local vars *)
  ]

let compile_fun_postlude (num_local_vars : int) : instruction list =
  [
    IAdd(Reg(RSP), Const(Int64.of_int (word_size * num_local_vars)));  (* Undoes the allocation *)
    IPop(Reg(RBP));
    IRet;
  ]

let rec compile_aexpr (e : tag aexpr) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  match e with
  | ALet(id, bind, body, _) -> 
    let compiled_bind = compile_cexpr bind env num_args is_tail in
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
     @ (compile_aexpr thn env num_args is_tail)
     @ [IJmp(lbl_done)]

     @ [ILabel(lbl_els)]
     @ (compile_aexpr els env num_args is_tail)
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
        | Print -> [
            IMov(Reg(RDI), body_imm);
            ICall("print");
          ]
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
  | CApp(fname, args, _) ->
    let padding = (if (List.length args) mod 2 = 0 then [] else [IPush(Sized(QWORD_PTR, Const(0L)))]) in
    let compiled_args = List.map
                       (fun arg ->
                          let compiled_imm = (compile_imm arg env) in
                          IPush(Sized(QWORD_PTR, compiled_imm)))
                       args
                       in
    let padded_comp_args = compiled_args @ padding in
    let num_args_passed = List.length padded_comp_args in
    (List.rev padded_comp_args)
    @
    [
    ICall(fname);
    IAdd(Reg(RSP), Const(Int64.of_int (word_size * num_args_passed)));
    ]
  | CImmExpr(expr) -> [IMov(Reg(RAX), (compile_imm expr env))]
and compile_imm e (env : arg envt) : arg =
  match e with
  | ImmNum(n, _) -> Const(Int64.shift_left n 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)

let compile_decl (d : tag adecl) (env : arg envt): instruction list =
  match d with
  | ADFun(fname, args, body, _) ->
    let num_body_vars = (deepest_stack body env) in
    let prelude = compile_fun_prelude fname args env num_body_vars in
    let compiled_body = compile_aexpr body env (List.length args) false in
    let postlude = compile_fun_postlude num_body_vars in
    prelude @ compiled_body @ postlude

let compile_prog ((anfed : tag aprogram), (env : arg envt)) : string =
  match anfed with
  | AProgram(decls, body, _) ->
      let compiled_decls =
        List.fold_left
          (fun accum_instrs decl ->
            accum_instrs
            (* basically a line of whitespace between function decls *)
            @ [ILineComment("")]
            @ (compile_decl decl env))
          [] decls in
      let num_prog_body_vars = (deepest_stack body env) in
      let compiled_body = (compile_aexpr body env num_prog_body_vars false) in
      let prelude =
        "section .text
extern error
extern print
extern error
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
        ] in
      let decl_assembly_string = (to_asm compiled_decls) in
      let body_assembly_string = (to_asm (stack_setup @ compiled_body @ postlude)) in
      sprintf "%s%s%s\n" prelude decl_assembly_string body_assembly_string 

(* Feel free to add additional phases to your pipeline.
   The final pipeline phase needs to return a string,
   but everything else is up to you. *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  |> (add_phase shortcircuit_rewrite and_or_rewrite)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase locate_bindings naive_stack_allocation)
  |> (add_phase result compile_prog)
;;
