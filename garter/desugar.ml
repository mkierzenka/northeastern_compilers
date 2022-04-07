open Printf
open Exprs
open Errors
open Util

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;; DESUGARING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)

let desugar (p : sourcespan program) : sourcespan program =
  let gensym =
    let next = ref 0 in
    (fun name ->
      next := !next + 1;
      sprintf "%s_%d" name (!next)) in
  let rec helpP (p : sourcespan program) =
    match p with
    | Program(decls, body, tag) ->
       (* This particular desugaring will convert declgroups into ELetRecs *)
       let merge_sourcespans ((s1, _) : sourcespan) ((_, s2) : sourcespan) : sourcespan = (s1, s2) in
       let wrap_G g body =
         match g with
         | [] -> body
         | f :: r ->
            let span = List.fold_left merge_sourcespans (get_tag_D f) (List.map get_tag_D r) in
            ELetRec(helpG g, body, span) in
       Program([], List.fold_right wrap_G decls (helpE body), tag)
  and helpG g =
    List.map helpD g
  and helpD d =
    match d with
    | DFun(name, args, body, tag) ->
       let helpArg a =
         match a with
         | BTuple(_, tag) ->
            let name = gensym "argtup" in
            let newbind = BName(name, false, tag) in
            (newbind, [(a, EId(name, tag), tag)])
         | _ -> (a, []) in
       let (newargs, argbinds) = List.split (List.map helpArg args) in
       let newbody = ELet(List.flatten argbinds, body, tag) in
       (BName(name, false, tag), ELambda(newargs, helpE newbody, tag), tag)
  and helpBE bind =
    let (b, e, btag) = bind in
    let e = helpE e in
    match b with
    | BTuple(binds, ttag) ->
       (match e with
        | EId _ ->
           expandTuple binds ttag e
        | _ ->
           let newname = gensym "tup" in
           (BName(newname, false, ttag), e, btag) :: expandTuple binds ttag (EId(newname, ttag)))
    | _ -> [(b, e, btag)]
  and expandTuple binds tag source : sourcespan binding list =
    let tupleBind i b =
      match b with
      | BBlank btag -> []
      | BName(_, _, btag) ->
        [(b, EGetItem(source, ENumber(Int64.of_int(i), dummy_span), tag), btag)]
      | BTuple(binds, tag) ->
          let newname = gensym "tup" in
          let newexpr = EId(newname, tag) in
          (BName(newname, false, tag), EGetItem(source, ENumber(Int64.of_int(i), dummy_span), tag), tag) :: expandTuple binds tag newexpr
    in
    let size_check = EPrim2(CheckSize, source, ENumber(Int64.of_int(List.length binds), dummy_span), dummy_span) in
    let size_check_bind = (BBlank(dummy_span), size_check, dummy_span) in
    size_check_bind::(List.flatten (List.mapi tupleBind binds))
  and helpE e =
    match e with
    | ESeq(e1, e2, tag) -> ELet([(BBlank(tag), helpE e1, tag)], helpE e2, tag)
    | ETuple(exprs, tag) -> ETuple(List.map helpE exprs, tag)
    | EGetItem(e, idx, tag) -> EGetItem(helpE e, helpE idx, tag)
    | ESetItem(e, idx, newval, tag) -> ESetItem(helpE e, helpE idx, helpE newval, tag)
    | EId(x, tag) -> EId(x, tag)
    | ENumber(n, tag) -> ENumber(n, tag)
    | EBool(b, tag) -> EBool(b, tag)
    | ENil(t, tag) -> ENil(t, tag)
    | EPrim1(op, e, tag) ->
       EPrim1(op, helpE e, tag)
    | EPrim2(op, e1, e2, tag) ->
       EPrim2(op, helpE e1, helpE e2, tag)
    | ELet(binds, body, tag) ->
       let newbinds = (List.map helpBE binds) in
       List.fold_right (fun binds body -> ELet(binds, body, tag)) newbinds (helpE body)
    | ELetRec(bindexps, body, tag) ->
       (* ASSUMES well-formed letrec, so only BName bindings *)
       let newbinds = (List.map (fun (bind, e, tag) -> (bind, helpE e, tag)) bindexps) in
       ELetRec(newbinds, helpE body, tag)
    | EIf(cond, thn, els, tag) ->
       EIf(helpE cond, helpE thn, helpE els, tag)
    | EApp(name, args, native, tag) ->
       EApp(helpE name, List.map helpE args, native, tag)
    | ELambda(binds, body, tag) ->
       let expandBind bind =
         match bind with
         | BTuple(_, btag) ->
            let newparam = gensym "tuparg" in
            (BName(newparam, false, btag), helpBE (bind, EId(newparam, btag), btag))
         | _ -> (bind, []) in
       let (params, newbinds) = List.split (List.map expandBind binds) in
       let newbody = List.fold_right (fun binds body -> ELet(binds, body, tag)) newbinds (helpE body) in
       ELambda(params, newbody, tag)

  in helpP p

(* let desugar_decl_arg_tups (p : sourcespan program) : sourcespan program =
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

(* Convert a function decl to a binding (lambda bound to name) *)
let decl_to_binding (decl : sourcespan decl) : sourcespan binding =
  match decl with
  | DFun(fname, fargs, fbody, floc) ->
    let bnd = BName(fname, false, floc) in
    let expr = ELambda(fargs, fbody, floc) in
    (bnd, expr, floc)

(* Desugar single decl group into a let-rec expression, wrapping the body *)
let desugar_decl_group (decls : sourcespan decl list) (body : sourcespan expr) : sourcespan expr =
  match decls with
  | [] -> body
  | DFun(fname, fargs, fbody, floc)::rest ->
    (* Still operate on whole list, we just split to check there is 1+ decl and get some loc info *)
    let decls_as_bindings = List.map decl_to_binding decls in
    ELetRec(decls_as_bindings, body, floc)

(* Desugar declaration groups into explicit let-rec bindings *)
let desugar_decl_groups_to_binds (p : sourcespan program) : sourcespan program =
  match p with
  | Program(decl_groups, body, loc) ->
      let new_body = List.fold_right desugar_decl_group decl_groups body in
      (* don't touch the body otherwise, just looking at decls *)
      Program([], new_body, loc)

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
  (desugar_decl_arg_tups p))))) *)
