open Printf
open Errors
open Exprs
open Pretty
open Phases

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


let check_scope (e : sourcespan expr) : sourcespan expr =
  let rec help e env =
    match e with
    | EBool _ -> ()
    | ENumber _ -> ()
    | EId (x, loc) ->
       (try ignore (List.assoc x env)
        with Not_found ->
             raise (BindingError(sprintf "The identifier %s, used at <%s>, is not in scope" x (string_of_sourcespan loc))))
    | EPrim1(_, e, _) -> help e env
    | EPrim2(_, l, r, _) -> help l env; help r env
    | EIf(c, t, f, _) -> help c env; help t env; help f env
    | ELet(binds, body, _) ->
       let (env2, _) =
         (List.fold_left
           (fun (scope_env, shadow_env) (x, e, loc) ->
             try
               let existing = List.assoc x shadow_env in
               raise (BindingError(sprintf "The identifier %s, defined at <%s>, shadows one defined at <%s>"
                                           x (string_of_sourcespan loc) (string_of_sourcespan existing)))
             with Not_found ->
               help e scope_env;
               ((x, loc)::scope_env, (x, loc)::shadow_env))
           (env, []) binds) in
       help body env2
  in help e []; e

let rec lookup_rename (x : string) (env : (string * string) list) : string =
  match env with
  | [] -> failwith (sprintf "Failed to lookup %s" x) (* should never happen, make sure to check_scope and tag first *)
  | (k, v) :: tail ->
      if k = x
      then v
      else lookup_rename x tail
;;

let rename (e : tag expr) : tag expr =
  let rec help (env : (string * string) list) (e : tag expr) : tag expr =
    match e with
    | EId(x, tag) -> EId((lookup_rename x env), tag)
    | ELet(binds, body, tag) ->
        let (newbinds, newenv) = bind_help env binds in
        let newbody = help newenv body in
        ELet(newbinds, newbody, tag)
    | ENumber(n, tag) -> ENumber(n, tag)
    | EBool(b, tag) -> EBool(b, tag)
    | EPrim1(op, e, t) -> EPrim1(op, (help env e), t)
    | EPrim2(op, e1, e2, t) -> EPrim2(op, (help env e1), (help env e2), t)
    | EIf(cond, thn, els, t) -> EIf((help env cond), (help env thn), (help env els), t)
  and bind_help (env : (string * string) list) (binds : tag bind list) : tag bind list * ((string * string) list) =
    match binds with
    | [] -> (binds, env)
    | (sym, expr, t) :: tail ->
        let newexpr = help env expr in
        let newsym = sprintf "%s#%d" sym t in
        let (newbinds, newenv) = bind_help ((sym, newsym) :: env) tail in
        ((newsym, newexpr, t) :: newbinds, newenv)
  in help [] e
;;

let tag (e : 'a expr) : tag expr =
  let rec help (e : 'a expr) (num : int) : (tag expr * tag) =
    match e with
    | EId(x, _) -> (EId(x, num), num + 1)
    | ENumber(n, _) -> (ENumber(n, num), num + 1)
    | EBool(b, _) -> (EBool(b, num), num + 1)
    | EPrim1(op, e, _) ->
       let (tag_e, new_n) = help e (num + 1) in
       (EPrim1(op, tag_e, num), new_n)
    | EPrim2(op, e1, e2, _) ->
       let (tag_e1, num_e1) = help e1 (num + 1) in
       let (tag_e2, num_e2) = help e2 (num_e1) in
       (EPrim2(op, tag_e1, tag_e2, num), num_e2)
    | ELet(binds, body, _) ->
       let (new_binds, num_binds) =
         List.fold_left
           (fun (rev_binds, next_num) (x, b, _) ->
             let (tag_b, num_b) = help b (next_num + 1) in
             ((x, tag_b, next_num)::rev_binds, num_b))
           ([], num + 1) binds in
       let (tag_body, num_body) = help body num_binds in
       (ELet(List.rev new_binds, tag_body, num), num_body)
    | EIf(cond, thn, els, _) ->
       let (tag_cond, num_cond) = help cond (num + 1) in
       let (tag_thn, num_thn) = help thn (num_cond) in
       let (tag_els, num_els) = help els (num_thn) in
       (EIf(tag_cond, tag_thn, tag_els, num), num_els)
  in let (ans, _) = help e 1
     in ans

let rec untag (e : 'a expr) : unit expr =
  match e with
  | EId(x, _) -> EId(x, ())
  | ENumber(n, _) -> ENumber(n, ())
  | EBool(b, _) -> EBool(b, ())
  | EPrim1(op, e, _) ->
     EPrim1(op, untag e, ())
  | EPrim2(op, e1, e2, _) ->
     EPrim2(op, untag e1, untag e2, ())
  | ELet(binds, body, _) ->
     ELet(List.map(fun (x, b, _) -> (x, untag b, ())) binds, untag body, ())
  | EIf(cond, thn, els, _) ->
     EIf(untag cond, untag thn, untag els, ())

let anf (e : tag expr) : unit expr =
  let rec helpC (e : tag expr) : (unit expr * (string * unit expr) list) = 
    match e with
    | EPrim1(op, arg, _) ->
       let (arg_imm, arg_setup) = helpI arg in
       (EPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, left, right, _) ->
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (EPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
       let (cond_imm, cond_setup) = helpI cond in
       (EIf(cond_imm, anf _then, anf _else, ()), cond_setup)
    | ENumber(n, _) -> (ENumber(n, ()), [])
    | EBool(b, _) -> (EBool(b, ()), [])
    | ELet([], body, _) -> helpC body
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    | EId(name, _) -> (EId(name, ()), [])
  and helpI (e : tag expr) : (unit expr * (string * unit expr) list) =
    match e with
    | EPrim1(op, arg, tag) ->
       let tmp = sprintf "unary_%d" tag in
       let (arg_imm, arg_setup) = helpI arg in
       (EId(tmp, ()), arg_setup @ [(tmp, EPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
       let tmp = sprintf "binop_%d" tag in
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (EId(tmp, ()), left_setup @ right_setup @ [(tmp, EPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (EId(tmp, ()), cond_setup @ [(tmp, EIf(cond_imm, anf _then, anf _else, ()))])
    | ENumber(n, _) -> (ENumber(n, ()), [])
    | EBool(b, _) -> (EBool(b, ()), [])
    | ELet([], body, _) -> helpI body
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    | EId(name, _) -> (EId(name, ()), [])
  and anf e = 
    let (ans, ans_setup) = helpI e in
    List.fold_right (fun (bind, exp) body -> ELet([bind, exp, ()], body, ())) ans_setup ans
  in
  anf e
;;

  
let r_to_asm (r : reg) : string =
  match r with
  | RAX -> "RAX"
  | RSI -> "RSI"
  | RDI -> "RDI"
  | RCX -> "RCX"
  | RDX -> "RDX"
  | RSP -> "RSP"
  | RBP -> "RBP"
  | R8  -> "R8"
  | R9  -> "R9"

let rec arg_to_asm (a : arg) : string =
  match a with
  | Const(n) -> sprintf "%Ld" n
  | HexConst(n) -> sprintf "QWORD 0x%Lx" n
  | Reg(r) -> r_to_asm r
  | RegOffset(n, r) ->
     if n >= 0 then
       sprintf "[%s+%d]" (r_to_asm r) (word_size * n)
     else
       sprintf "[%s-%d]" (r_to_asm r) (-1 * word_size * n)
  | Sized(size, a) ->
     sprintf "%s %s"
             (match size with | QWORD_PTR -> "QWORD" | DWORD_PTR -> "DWORD" | WORD_PTR -> "WORD" | BYTE_PTR -> "BYTE")
             (arg_to_asm a)

let rec i_to_asm (i : instruction) : string =
  match i with
  | IMov(dest, value) ->
     sprintf "  mov %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IAdd(dest, to_add) ->
     sprintf "  add %s, %s" (arg_to_asm dest) (arg_to_asm to_add)
  | ISub(dest, to_sub) ->
     sprintf "  sub %s, %s" (arg_to_asm dest) (arg_to_asm to_sub)
  | IMul(dest, to_mul) ->
     sprintf "  imul %s, %s" (arg_to_asm dest) (arg_to_asm to_mul)
  | ICmp(left, right) ->
     sprintf "  cmp %s, %s" (arg_to_asm left) (arg_to_asm right)
  | ILabel(name) ->
     name ^ ":"
  | IJo(label) ->
     sprintf "  jo %s" label
  | IJe(label) ->
     sprintf "  je %s" label
  | IJne(label) ->
     sprintf "  jne %s" label
  | IJl(label) ->
     sprintf "  jl %s" label
  | IJle(label) ->
     sprintf "  jle %s" label
  | IJg(label) ->
     sprintf "  jg %s" label
  | IJge(label) ->
     sprintf "  jge %s" label
  | IJmp(label) ->
     sprintf "  jmp %s" label
  | IJz(label) ->
     sprintf "  jz %s" label
  | IJnz(label) ->
     sprintf "  jnz %s" label
  | IAnd(dest, value) ->
     sprintf "  and %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IOr(dest, value) ->
     sprintf "  or %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IXor(dest, value) ->
     sprintf "  xor %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IShl(dest, value) ->
     sprintf "  shl %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IShr(dest, value) ->
     sprintf "  shr %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | ISar(dest, value) ->
     sprintf "  sar %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IPush(value) ->
     sprintf "  push %s" (arg_to_asm value)
  | IPop(dest) ->
     sprintf "  pop %s" (arg_to_asm dest)
  | ICall(label) ->
     sprintf "  call %s" label
  | IRet ->
     "  ret"
  | ITest(arg, comp) ->
     sprintf "  test %s, %s" (arg_to_asm arg) (arg_to_asm comp)
  | ILineComment(str) ->
     sprintf "  ;; %s" str
  | IInstrComment(instr, str) ->
     sprintf "%s ; %s" (i_to_asm instr) str

let to_asm (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (i_to_asm i)) "" is

let rec find (ls : (string * 'a) list) (x : string) : 'a =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y,v)::rest ->
     if y = x then v else find rest x

(* NOTE: Assumes that e is in ANF *)
let rec count_vars (e : 'a expr) =
  match e with
  | EIf(_, t, f, _) -> max (count_vars t) (count_vars f)
  | ELet([_, b, _], body, _) ->
     1 + (max (count_vars b) (count_vars body))
  | _ -> 0

let rec replicate (x : 'a) (i : int) : 'a list =
  if i = 0 then []
  else x :: (replicate x (i - 1))


(* Compiled Type Checking *)
let check_rax_for_num (err_lbl : string) : instruction list =
  [
   (* this "test" trick depends on num_tag being 0 *)
   ITest(Reg(RAX), HexConst(num_tag_mask));
   IJnz(err_lbl);
  ]

let check_rax_for_bool (err_lbl : string) : instruction list =
  [
   (* Operate on temp register R8 instead of RAX. This is because we call AND
    * on the register, which will alter the value. We want to preserve the value
    * in RAX, hence we operate on R8 instead *)
   IMov(Reg(R8), Reg(RAX));
   IAnd(Reg(R8), HexConst(bool_tag_mask));
   ICmp(Reg(R8), HexConst(bool_tag));
   IJnz(err_lbl);
  ]

let check_for_overflow = [IJo("err_OVERFLOW")]


let rec compile_expr (e : tag expr) (si : int) (env : (string * int) list) : instruction list =
  match e with
  | ELet([id, e, _], body, _) ->
     let prelude = compile_expr e (si + 1) env in
     let body = compile_expr body (si + 1) ((id, si)::env) in
     prelude
     @ [ IMov(RegOffset(~-si, RBP), Reg(RAX)) ]
     @ body
  | EPrim1(op, e, tag) ->
     let e_reg = compile_imm e env in
     begin match op with
       | Add1 ->
           [IMov(Reg(RAX), e_reg)]
           @ (check_rax_for_num "err_ARITH_NOT_NUM")
           @ [IAdd(Reg(RAX), Const(2L))]
           @ check_for_overflow
       | Sub1 ->
           [IMov(Reg(RAX), e_reg)]
           @ (check_rax_for_num "err_ARITH_NOT_NUM")
           @ [ISub(Reg(RAX), Const(2L))]
           @ check_for_overflow
        | Print -> [
            IMov(Reg(RDI), e_reg);
            ICall("print");
          ]
        | IsBool ->
          let true_lbl = sprintf "is_bool_true_%d" tag in
          let false_lbl = sprintf "is_bool_false_%d" tag in
          let done_lbl = sprintf "is_bool_done_%d" tag in
          [
           IMov(Reg(RAX), e_reg);
           (* we don't need to save RAX on the stack because we overwrite the
            * value with true/false later *)
           IAnd(Reg(RAX), HexConst(bool_tag_mask));
           ICmp(Reg(RAX), HexConst(bool_tag));
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
           IMov(Reg(RAX), e_reg);
           (* this "test" trick depends on num_tag being 0 *)
           ITest(Reg(RAX), HexConst(num_tag_mask));
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
           [IMov(Reg(RAX), e_reg)]
           @ (check_rax_for_bool "err_LOGIC_NOT_BOOL")
           @ [IXor(Reg(RAX), bool_mask)]
        | PrintStack ->
            (* TODO *)
            raise (NotYetImplemented "PrintStack not yet implemented")
     end
  | EPrim2(op, lhs, rhs, tag) ->
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
         @ [IAdd(Reg(RAX), rhs_reg)]
         @ check_for_overflow
      | Minus ->
         (* check rhs for numerical val *)
         [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_num "err_ARITH_NOT_NUM")
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num "err_ARITH_NOT_NUM")
         @ [ISub(Reg(RAX), rhs_reg)]
         @ check_for_overflow
      | Times ->
         (* check rhs for numerical val *)
         [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_num "err_ARITH_NOT_NUM")
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num "err_ARITH_NOT_NUM")
         @ [IMul(Reg(RAX), rhs_reg)]
         @ check_for_overflow
      | And ->
         let lbl_lhs = sprintf "and_lhs_%d" tag in
         let lbl_rhs = sprintf "and_rhs_%d" tag in
         let lbl_done = sprintf "and_done_%d" tag in

         (* LHS *)
         [ILabel(lbl_lhs)]
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_bool "err_LOGIC_NOT_BOOL")
         (* test for short circuit: if RAX is false then we're done *)
         (* need to use temp register R8 because Test cannot accept a 64 bit immediate *)
         @ [IMov(Reg(R8), bool_mask)]
         @ [ITest(Reg(RAX), Reg(R8))]
         @ [IJz(lbl_done)]

         (* RHS *)
         (* don't need to perform the AND because we know LHS is true *)
         @ [ILabel(lbl_rhs)]
         @ [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_bool "err_LOGIC_NOT_BOOL")

         (* done *)
         @ [ILabel(lbl_done)]
      | Or -> raise (NotYetImplemented "Fill in here")
      | Greater -> raise (NotYetImplemented "Fill in here")
      | GreaterEq -> raise (NotYetImplemented "Fill in here")
      | Less -> raise (NotYetImplemented "Fill in here")
      | LessEq -> raise (NotYetImplemented "Fill in here")
      | Eq -> raise (NotYetImplemented "Fill in here")
     end
  | EIf _ -> raise (NotYetImplemented "Fill in here")
  | ENumber(n, _) -> [ IMov(Reg(RAX), compile_imm e env) ]
  | EBool(n, _) -> [ IMov(Reg(RAX), compile_imm e env) ]
  | EId(x, _) -> [ IMov(Reg(RAX), compile_imm e env) ]
  | _ -> raise (InternalCompilerError "Impossible: Not in ANF")
and compile_imm (e : tag expr) (env : (string * int) list) : arg =
  match e with
  | ENumber(n, _) ->
     if n > (Int64.div Int64.max_int 2L) || n < (Int64.div Int64.min_int 2L) then
       raise (IntegerOverflowError (Int64.to_string n))
     else
       Const(Int64.mul n 2L)
  | EBool(true, _) -> const_true
  | EBool(false, _) -> const_false
  | EId(x, _) -> RegOffset(~-(find env x), RBP)
  | _ -> raise (InternalCompilerError "Impossible: not an immediate")
;;

let compile_prog (anfed : tag expr) : string =
  let prelude =
    "section .text
extern error
extern print
global our_code_starts_here" in
  let num_vars = (count_vars anfed) in
  let stack_setup = [
      ILabel("our_code_starts_here");
      IPush(Reg(RBP));
      IMov(Reg(RBP), Reg(RSP));
      ISub(Reg(RSP), Const(Int64.of_int (word_size * num_vars)))  (* allocates stack space for all local vars *)
    ] in
  let postlude = [
      ILabel("program_done");
      IAdd(Reg(RSP), Const(Int64.of_int (word_size * num_vars)));  (* Undoes the allocation *)
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
  let body = (compile_expr anfed 1 []) in
  let as_assembly_string = (to_asm (stack_setup @ body @ postlude)) in
  sprintf "%s%s\n" prelude as_assembly_string

let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_phase well_formed check_scope)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename)
  |> (add_phase anfed (fun p -> tag (anf p)))
  |> (add_phase result compile_prog)
;;
