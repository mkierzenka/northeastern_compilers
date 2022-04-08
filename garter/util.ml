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
