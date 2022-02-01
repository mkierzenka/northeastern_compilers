open Printf
open Sexp

(* Abstract syntax of (a small subset of) x86 assembly instructions *)

let word_size = 8
;;
       
type reg =
  | RAX
  | RSP

type arg =
  | Const of int64
  | Reg of reg
  | RegOffset of int * reg (* int is # words of offset *)

type instruction =
  | IMov of arg * arg
  | IAdd of arg * arg
  | IRet

(* Concrete syntax of the Adder language:

‹expr›:
  | NUMBER
  | IDENTIFIER
  | ( let ( ‹bindings› ) ‹expr› )
  | ( add1 ‹expr› )
  | ( sub1 ‹expr› )
‹bindings›:
  | ( IDENTIFIER ‹expr› )
  | ( IDENTIFIER ‹expr› ) ‹bindings›

 *)


(* Abstract syntax of the Adder language *)

type prim1 =
  | Add1
  | Sub1

type 'a expr =
  | Number of int64 * 'a
  | Id of string * 'a
  | Let of (string * 'a expr) list * 'a expr * 'a
  | Prim1 of prim1 * 'a expr * 'a

let expr_info (expr : 'a expr) =
  match expr with
    | Number (_, x) -> x
    | Id (_, x) -> x
    | Let (_, _, x) -> x
    | Prim1 (_, _, x) -> x
;;

(* Helper function for easily creating error messages that include the error position *)
let create_err (errt : string) (msg : string) pos (range : bool) : string =
  sprintf "%s error %s, %s" errt (pos_to_string pos range) msg
;;

(* Function to convert from unknown s-expressions to Adder exprs
   Throws a SyntaxError message if there's a problem
 *)
exception SyntaxError of string
let rec expr_of_sexp (s : pos sexp) : pos expr =
  match s with
    | Int(x, pos) -> Number(x,pos)
    | Sym(x, pos) -> Id(x, pos)
    | Nest(l, pos) ->
        (match l with
          | [Sym("add1", pos); expr] ->
              Prim1(Add1, (expr_of_sexp expr), pos)
          | [Sym("sub1", pos); expr] ->
              Prim1(Sub1, (expr_of_sexp expr), pos)
          | [Sym("let", lpos); Nest(bs, bpos); expr] ->
              Let((bindings bs), (expr_of_sexp expr), lpos)
          | _ -> raise (SyntaxError (create_err "Syntax" "paren must be followed by let, add, or sub" pos false)))
    | Bool (_, pos) -> raise (SyntaxError (create_err "Syntax" "boolean values are not supported by adder" pos false))
  and bindings (bs : pos sexp list) : (string * pos expr) list =
    match bs with
      | [] -> []
      | Nest([Sym(id, ipos); expr], npos) :: tail ->
          (id, (expr_of_sexp expr)) :: (bindings tail)
      | other_sexp :: tail -> raise (SyntaxError (create_err "Syntax" "expected list of let bindings" (sexp_info other_sexp) false))
;;
  

(* Functions that implement the compiler *)

(* The next four functions convert assembly instructions into strings,
   one datatype at a time.  Only one function has been fully implemented
   for you. *)
let reg_to_asm_string (r : reg) : string =
  match r with
    | RAX -> "RAX"
    | RSP -> "RSP"

let arg_to_asm_string (a : arg) : string =
  match a with
  | Const(n) -> sprintf "%Ld" n
  | Reg reg -> reg_to_asm_string reg
  | RegOffset(offs, reg) -> sprintf "[%d + %s]" offs (reg_to_asm_string reg)

let instruction_to_asm_string (i : instruction) : string =
  match i with
  | IMov(dest, value) ->
     sprintf "\tmov %s, %s" (arg_to_asm_string dest) (arg_to_asm_string value)
  | IAdd(dest, add) ->
     sprintf "\tadd %s, %s" (arg_to_asm_string dest) (arg_to_asm_string add)
  | IRet -> "\tret"

let to_asm_string (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (instruction_to_asm_string i)) "" is

(* A helper function for looking up a name in a "dictionary" and 
   returning the associated value if possible.  This is definitely
   not the most efficient data structure for this, but it is nice and simple... *)
let rec find (ls : (string * 'a) list) (x : string) : 'a option =
  match ls with
  | [] -> None
  | (y, v)::rest ->
     if y = x then Some(v) else find rest x

(* Wrapper around find to easily check if a symbol is in an environment *)
let in_env (ls : (string * 'a) list) (x : string) : bool =
  match (find ls x) with
  | None -> false
  | Some _ -> true

(* The exception to be thrown when some sort of problem is found with names *)
exception BindingError of string
(* The actual compilation process.  The `compile` function is the primary function,
   and uses `compile_env` as its helper.  In a more idiomatic OCaml program, this
   helper would likely be a local definition within `compile`, but separating it out
   makes it easier for you to test it. *)
let rec compile_env
          (p : pos expr)         (* the program, currently annotated with source location info *)
          (stack_index : int)    (* the next available stack index *)
          (env : (string * int) list) (* the current binding environment of names to stack slots *)
        : instruction list =     (* the instructions that would execute this program *)
  match p with
  | Number(n, _) ->
     [
       IMov(Reg(RAX), Const(n))
     ]
  | Prim1(Add1, expr, _) ->
     (compile_env expr stack_index env) @
     [
       IAdd(Reg(RAX), Const(1L))
     ]
  | Prim1(Sub1, expr, _) ->
     (compile_env expr stack_index env) @
     [
       IAdd(Reg(RAX), Const(-1L))
     ]
  | Let(decls, expr, _) ->
      let (let_sidx, let_env, let_instr) = add_letenv decls stack_index env []
      in let_instr @ (compile_env expr let_sidx let_env)
  | Id(sym, pos) -> 
      match (find env sym) with
	    | None -> raise (BindingError (create_err "Binding" (sprintf "Unbound symbol: %s" sym) pos false))
		| Some(offset) -> [IMov(Reg(RAX), RegOffset(~-1*word_size*offset, RSP))]

 and add_letenv
        (decls : (string * pos expr) list)
        (sidx : int)
        (env : (string * int) list)
        (instr : instruction list)
       : (int * ((string * int) list) * (instruction list)) =
   match decls with
    | [] -> (sidx, env, instr)
    | (sym, expr) :: tail ->
        if (in_env env sym)
        then raise (BindingError (create_err "Binding" (sprintf "Duplicate symbol %s" sym) (expr_info expr) false))
        else let newhead = (sym, sidx)
             in  add_letenv tail (sidx+1) (newhead :: env)
                    (instr @
					 (compile_env expr (sidx+1) env) @ (* TODO get rid of +1? *)
                     [IMov(RegOffset(~-1*word_size*sidx, RSP), Reg(RAX))])

let compile (p : pos expr) : instruction list =
  compile_env p 1 [] (* Start at the first stack slot, with an empty environment *)

(* The entry point for the compiler: a function that takes a expr and
   creates an assembly-program string representing the compiled version *)
let compile_to_string (prog : pos expr) : string =
  let prelude = "
section .text
global our_code_starts_here
our_code_starts_here:" in
  let asm_string = (to_asm_string ((compile prog) @ [IRet])) in
  let asm_program = sprintf "%s%s\n" prelude asm_string in
  asm_program

