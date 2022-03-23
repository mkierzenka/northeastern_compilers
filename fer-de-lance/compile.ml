open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
(* Add at least one of these two *)
       
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
    | Program(decls, body, tag) ->
       Program(List.map (fun group -> List.map (helpD env) group) decls, helpE env body, tag)
  and helpD env decl =
    match decl with
    | DFun(name, args, body, tag) ->
       let (newArgs, env') = helpBS env args in
       DFun(name, newArgs, helpE env' body, tag)
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
    | ALetRec(binds, body, _) -> List.fold_left max (helpA body) (List.map (fun (_, bind) -> helpC bind) binds)
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
    | EApp(func, args, _, _) ->
       raise (NotYetImplemented("Revise this case"))
    | ETuple(args, _) ->
       raise (NotYetImplemented("Finish this case"))
    | EGetItem(tup, idx, _) ->
       raise (NotYetImplemented("Finish this case"))
    | ESetItem(tup, idx, newval, _) ->
       raise (NotYetImplemented("Finish this case"))
         
    | ELambda(binds, body, _) ->
       raise (NotYetImplemented("Finish this case"))
    | ELetRec(binds, body, _) ->
       raise (NotYetImplemented("Finish this case"))

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
       raise (NotYetImplemented("Finish this case"))
       (* Hint: use BLet to bind the result *)
    | EGetItem(tup, idx, tag) ->
       raise (NotYetImplemented("Finish this case"))
    | ESetItem(tup, idx, newval, tag) ->
       raise (NotYetImplemented("Finish this case"))

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
    | EApp(func, args, _, tag) ->
       raise (NotYetImplemented("Revise this case"))
    | ELet([], body, _) -> helpI body
    | ELet((BBlank _, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpI exp in (* MUST BE helpI, to avoid any missing final steps *)
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ body_setup)
    | ELambda(binds, body, tag) ->
       raise (NotYetImplemented("Finish this case"))
       (* Hint: use BLet to bind the answer *)
    | ELet((BName(bind, _, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet(bind, exp_ans)] @ body_setup)
    | ELet((BTuple(binds, _), exp, _)::rest, body, pos) ->
       raise (InternalCompilerError("Tuple bindings should have been desugared away"))
    | ELetRec(binds, body, tag) ->
       raise (NotYetImplemented("Finish this case"))
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


let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  let rec wf_E (e : sourcespan expr) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement well-formedness checking for expressions"])
  and wf_D (d : sourcespan decl) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement well-formedness checking for definitions"])
  in
  match p with
  | Program(decls, body, _) ->
     Error([NotYetImplemented "Implement well-formedness checking for programs"])
;;


(*
let desugar (p : sourcespan program) : sourcespan program =
  let gensym =
    let next = ref 0 in
    (fun name ->
      next := !next + 1;
      sprintf "%s_%d" name (!next)) in
  let rec helpE (e : sourcespan expr) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement desugaring for expressions"])
  and helpD (d : sourcespan decl) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement desugaring for definitions"])
  in
  match p with
  | Program(decls, body, _) ->
      raise (NotYetImplemented "Implement desugaring for programs")
;;
*)
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

let desugar_print_to_app (p : sourcespan program) : sourcespan program =
  let rec help_decl (d : sourcespan decl) : sourcespan decl =
    match d with
    | DFun(fname, args, body, loc) ->
        DFun(fname, args, help_expr body, loc)
  and help_expr (e : sourcespan expr) : sourcespan expr =
    match e with
    | EPrim1(Print, expr, loc) -> EApp(EId("print", loc), [help_expr expr], Native, loc)
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
      let innerHelpD = fun decls -> List.map help_decl decls in
      let rw_decls = List.map innerHelpD decls in
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

let free_vars (e: 'a aexpr) : string list =
  raise (NotYetImplemented "Implement free_vars for expressions")
;;


let naive_stack_allocation (prog: tag aprogram) : tag aprogram * arg envt =
  (*
   * TODO: delete this.
  let rec help_decl (decl : tag adecl) (env : arg envt) : arg envt =
    match decl with
    | ADFun(fname, args, body, _) ->
        let args_with_idx = List.mapi (fun i arg -> (arg, RegOffset((i + 2)*word_size, RBP))) args in
        let new_env = List.fold_left (fun accum_env cell -> cell :: accum_env) env args_with_idx in
        let (decl_env, _) = help_aexpr body 1 new_env in
        decl_env
  *)
  (* TODO add in code for handing our new C*/A* items, such as ALetRec *)
  let rec help_aexpr (body : tag aexpr) (si : int) (env : arg envt) : arg envt * int =
    match body with
    | ASeq(cexp, aexp, _) -> raise (NotYetImplemented "ASeq stack allocation not yet implemented")
    | ALet(sym, bind, body, _) ->
        let newenv = (sym, RegOffset(~-si*word_size, RBP)) :: env in
        let (bindenv, newsi) = help_cexpr bind (si+1) newenv in
        help_aexpr body newsi bindenv
    | ALetRec(binds, body, _) -> raise (NotYetImplemented "ALetRec stack allocation not yet implemented")
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
    | CLambda(args, body, _) -> raise (NotYetImplemented "CLambda stack allocation not yet implemented")
  in
  match prog with
  | AProgram(body, _) ->
      let (prog_env, _) = help_aexpr body 1 [] in
      (prog, prog_env)
;;

let rec compile_fun (fun_name : string) args body env : instruction list =
  raise (NotYetImplemented "Compile funs not yet implemented")
and compile_aexpr (e : tag aexpr) (si : int) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  raise (NotYetImplemented "Compile aexpr not yet implemented")
and compile_cexpr (e : tag cexpr) si env num_args is_tail =
  raise (NotYetImplemented "Compile cexpr not yet implemented")
and compile_imm e env =
  match e with
  | ImmNum(n, _) -> Const(Int64.shift_left n 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)
  | ImmNil(_) -> raise (NotYetImplemented "Finish this")

let compile_prog ((anfed : tag aprogram), (env: arg envt)) : string =
  match anfed with
  | AProgram(body, _) ->
     let (body_prologue, comp_body, body_epilogue) = raise (NotYetImplemented "... do stuff with body ...") in
     
     let heap_start = [
         ILineComment("heap start");
         IInstrComment(IMov(Sized(QWORD_PTR, Reg(heap_reg)), Reg(List.nth first_six_args_registers 0)), "Load heap_reg with our argument, the heap pointer");
         IInstrComment(IAdd(Sized(QWORD_PTR, Reg(heap_reg)), Const(15L)), "Align it to the nearest multiple of 16");
         IMov(Reg scratch_reg, HexConst(0xFFFFFFFFFFFFFFF0L));
         IInstrComment(IAnd(Sized(QWORD_PTR, Reg(heap_reg)), Reg scratch_reg), "by adding no more than 15 to it")
       ] in
     let main = to_asm (body_prologue @ heap_start @ comp_body @ body_epilogue) in
     
     raise (NotYetImplemented "... combine main with any needed extra setup and error handling ...")
           
(* Feel free to add additional phases to your pipeline.
   The final pipeline phase needs to return a string,
   but everything else is up to you. *)


let run_if should_run f =
  if should_run then f else no_op_phase
;;

(* Add at least one desugaring phase somewhere in here *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  |> (add_phase desugared desugar)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename_and_tag)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase locate_bindings naive_stack_allocation)
  |> (add_phase result compile_prog)
;;
