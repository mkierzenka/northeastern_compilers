open Printf
(* open Pretty
open Phases *)
open Exprs
(* open Assembly *)
open Errors

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
       let (args_anses, args_setups) = List.split (List.map helpI args) in
       (CApp(func_ans, args_anses, ct, ()), func_setup @ (List.concat args_setups))
    | ETuple(args, _) ->
       let (args_anses, args_setups) = List.split (List.map helpI args) in
       (CTuple(args_anses, ()), List.concat args_setups)
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
       let tmp = sprintf "lambda_%d" tag in
       let (ans, setup) = helpC e in
       (ImmId(tmp, ()), setup @ [BLet(tmp, ans)])
    | ELet((BName(bind, _, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet(bind, exp_ans)] @ body_setup)
    | ELet((BTuple(binds, _), exp, _)::rest, body, pos) ->
       raise (InternalCompilerError("Tuple bindings should have been desugared away"))
    | ELetRec(binds, body, tag) ->
       let (body_ans, body_setup) = helpI body in
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
            binds in
       (* TODO- how to convert ELetRec into a CExpr for binding...? *)
       (body_ans, bindings_setups @ [BLetRec(new_bindings)] @ body_setup)
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
