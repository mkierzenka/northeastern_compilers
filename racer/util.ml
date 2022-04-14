open Printf
(* open Pretty
open Phases *)
open Exprs
open Assembly
open Errors

module StringSet = Set.Make(String)

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos)

let prim_bindings = []

let native_fun_bindings = [("input", (dummy_span, Some 0, Some 0))]
(* scope_info name_envt *)

(* you can add any functions or data defined by the runtime here for future use *)
let initial_val_env = []

let initial_fun_env = prim_bindings @ native_fun_bindings

(* type 'a envt = (string * 'a) list *)
type 'a name_envt = (string * 'a) list
type 'a tag_envt  = (tag * 'a) list

let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y,v)::rest ->
     if y = x then v else find rest x

let rec find_decl (ds : 'a decl list) (name : string) : 'a decl option =
  match ds with
    | [] -> None
    | (DFun(fname, _, _, _) as d)::ds_rest ->
      if name = fname then Some(d) else find_decl ds_rest name

let rec find_one (l : 'a list) (elt : 'a) : bool =
  match l with
    | [] -> false
    | x::xs -> (elt = x) || (find_one xs elt)

let rec find_opt (env : 'a name_envt) (elt: string) : 'a option =
  match env with
  | [] -> None
  | (x, v) :: rst -> if x = elt then Some(v) else find_opt rst elt

let add_var_to_env (name : string) (value : arg) (env_name : string) (env : arg name_envt name_envt) : arg name_envt name_envt =
  let sub_env = find env env_name in
  (env_name, ((name, value)::sub_env))::env



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
    | CSetItem(tup, idx, newval, _) -> StringSet.union (StringSet.union (help_imm tup seen) (help_imm idx seen)) (help_imm newval seen)
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

(* Compute the sets of free_vars at every node of an AST *)
let free_vars_cache (prog : 'a aprogram) : StringSet.t aprogram =
  let rec help_aexpr (expr : 'a aexpr) (seen : StringSet.t) : StringSet.t aexpr =
    match expr with
    | ASeq(lhs, rhs, _) ->
      let new_lhs = (help_cexpr lhs seen) in
      let new_rhs = (help_aexpr rhs seen) in
      ASeq(new_lhs, new_rhs, (StringSet.union (get_tag_C new_lhs) (get_tag_A new_rhs)))
    | ALet(bnd_name, bnd_exp, body, _) ->
      let new_bnd_exp = help_cexpr bnd_exp seen in
      let new_body = help_aexpr body (StringSet.add bnd_name seen) in
      let new_free = StringSet.union (get_tag_C new_bnd_exp) (get_tag_A new_body) in
      ALet(bnd_name, new_bnd_exp, new_body, new_free)
    | ALetRec(binds, body, _) ->
      let names = List.map fst binds in
      let names_set = StringSet.of_list names in
      let seen_with_names = StringSet.union names_set seen in
      let new_binds = List.map (fun (name, expr) -> (name, (help_cexpr expr seen_with_names))) binds in
      let new_binds_free = List.fold_left (fun free_acc (_, expr) -> StringSet.union free_acc (get_tag_C expr)) StringSet.empty new_binds in
      let new_body = help_aexpr body seen_with_names in
      let new_body_free = get_tag_A new_body in
      ALetRec(new_binds, new_body, StringSet.union new_binds_free new_body_free)
    | ACExpr(exp) -> ACExpr(help_cexpr exp seen)
  and help_cexpr (expr : 'a cexpr) (seen : StringSet.t) : StringSet.t cexpr =
    match expr with
    | CIf(cond, thn, els, _) ->
      let new_cond = help_imm cond seen in
      let new_thn = help_aexpr thn seen in
      let new_els = help_aexpr els seen in
      let new_free = StringSet.union (StringSet.union (get_tag_I new_cond) (get_tag_A new_thn)) (get_tag_A new_els) in
      CIf(new_cond, new_thn, new_els, new_free)
    | CScIf(fst, snd, thd, _) ->
      let new_fst = help_imm fst seen in
      let new_snd = help_aexpr snd seen in
      let new_thd = help_aexpr thd seen in
      let new_free = StringSet.union (StringSet.union (get_tag_I new_fst) (get_tag_A new_snd)) (get_tag_A new_thd) in
      CScIf(new_fst, new_snd, new_thd, new_free)
    | CPrim1(op, exp, _) ->
      let new_exp = help_imm exp seen in
      CPrim1(op, new_exp, (get_tag_I new_exp))
    | CPrim2(op, lhs, rhs, _) ->
      let new_lhs = help_imm lhs seen in
      let new_rhs = help_imm rhs seen in
      CPrim2(op, new_lhs, new_rhs, StringSet.union (get_tag_I new_lhs) (get_tag_I new_rhs))
    | CApp(func, args, ct, _) ->
      let new_func = (help_imm func seen) in
      let new_args = List.map (fun arg -> help_imm arg seen) args in
      let new_free = StringSet.union
        (get_tag_I new_func)
        (List.fold_left (fun free_acc new_arg -> StringSet.union free_acc (get_tag_I new_arg)) StringSet.empty new_args) in
      CApp(new_func, new_args, ct, new_free)
    | CImmExpr(exp) -> CImmExpr(help_imm exp seen)
    | CTuple(elems, _) ->
      let new_elems = List.map (fun arg -> help_imm arg seen) elems in
      let new_free = List.fold_left (fun free_acc elem -> StringSet.union free_acc (get_tag_I elem)) StringSet.empty new_elems in
      CTuple(new_elems, new_free)
    | CGetItem(tup, idx, _) ->
      let new_tup = (help_imm tup seen) in
      let new_idx = (help_imm idx seen) in
     CGetItem(new_tup, new_idx, StringSet.union (get_tag_I new_tup) (get_tag_I new_idx))
    | CSetItem(tup, idx, newval, _) ->
      let new_tup = (help_imm tup seen) in
      let new_idx = (help_imm idx seen) in
      let new_newval = (help_imm newval seen) in
     CSetItem(new_tup, new_idx, new_newval, StringSet.union (StringSet.union (get_tag_I new_tup) (get_tag_I new_idx)) (get_tag_I new_newval))
    | CLambda(args, body, _) ->
      let args_set = StringSet.of_list args in
      let seen_with_args = StringSet.union args_set seen in
      let new_body = help_aexpr body seen_with_args in
      CLambda(args, new_body, (get_tag_A new_body))
  and help_imm (expr : 'a immexpr) (seen : StringSet.t) : StringSet.t immexpr =
    match expr with
    | ImmNum(i, _) -> ImmNum(i, StringSet.empty)
    | ImmBool(b, _) -> ImmBool(b, StringSet.empty)
    | ImmId(name, _) -> ImmId(name, if StringSet.mem name seen then StringSet.empty else StringSet.singleton name)
    | ImmNil(_) -> ImmNil(StringSet.empty)
  in
  match prog with
  | AProgram(body, _) ->
    let new_body = help_aexpr body StringSet.empty in
    AProgram(new_body, get_tag_A new_body)
