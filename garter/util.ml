open Printf
(* open Pretty
open Phases *)
open Exprs
open Assembly
open Errors

module StringSet = Set.Make(String)

let prim_bindings = []

let native_fun_bindings = []

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

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos)

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
