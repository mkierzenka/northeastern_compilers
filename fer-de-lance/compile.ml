open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
open Well_formed
open Desugar
open Rename_and_tag
open Anf
open Naive_stack_allocation
open Util

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
let err_BAD_INPUT        = 18L
let err_TUP_IDX_NOT_NUM  = 19L


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

(* Returns the stack-index (in words) of the deepest stack index used for any 
   of the variables in this expression *)
let rec deepest_stack e env =
  let rec helpA e =
    match e with
    | ALet(name, bind, body, _) -> List.fold_left max 0 [name_to_offset name; helpC bind; helpA body]
    | ALetRec(binds, body, _) -> List.fold_left max (helpA body) (List.map (fun (name, bind) -> (max (helpC bind) (name_to_offset name))) binds)
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

(* Find all free variables *)
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
;;



(* Compiled Type Checking *)
let check_rax_for_num (err_lbl : string) : instruction list =
  [
   (* This "test" trick depends on num_tag being 0. R8 used because Test doesn't support imm64 *)
   ILineComment("check_rax_for_num (" ^ err_lbl ^ ")");
   IMov(Reg(R8), HexConst(num_tag_mask));
   ITest(Reg(RAX), Reg(R8));
   IJnz(Label(err_lbl));
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
   IJnz(Label(err_lbl));
  ]

let check_for_overflow = [IJo(Label("err_OVERFLOW"))]


let check_rax_for_tup (err_lbl : string) : instruction list =
  [
   (* Operate on temp register R8 instead of RAX. This is because we call AND
    * on the register, which will alter the value. We want to preserve the value
    * in RAX, hence we operate on R8 instead. R9 is used as intermediate because
      And, Cmp don't work on imm64s *)
   ILineComment("check_rax_for_tup (" ^ err_lbl ^ ")");
   IMov(Reg(R8), Reg(RAX));
   IMov(Reg(R9), HexConst(tuple_tag_mask));
   IAnd(Reg(R8), Reg(R9));
   IMov(Reg(R9), HexConst(tuple_tag));
   ICmp(Reg(R8), Reg(R9));
   IJne(Label(err_lbl));
  ]

let check_rax_for_nil (err_lbl : string) : instruction list =
  [
   ILineComment("check_rax_for_nil (" ^ err_lbl ^ ")");
   IMov(Reg(R8), const_nil);
   ICmp(Reg(RAX), Reg(R8));
   IJe(Label(err_lbl));
  ]


(* RAX should be the snakeval of the index (in a tuple)*)
(* DO NOT MODIFY RAX *)
let check_rax_for_tup_smaller (err_lbl : string) : instruction list =
  [
   ILineComment("check_rax_for_tup_smaller (" ^ err_lbl ^ ")");
   ICmp(Reg(RAX), Const(0L));
   (* no temp register because imm32 0 will be "sign-extended to imm64", which should still be 0 *)
   IJl(Label(err_lbl));
  ]


(* RAX should be the snakeval of the index (in a tuple)*)
(* DO NOT MODIFY RAX *)
let check_rax_for_tup_bigger (tup_address : arg) (err_lbl : string) : instruction list =
  [
   (* R8 is used as intermediate because Cmp don't work on imm64s *)
   ILineComment("check_rax_for_tup_bigger (" ^ err_lbl ^ ")");
   IMov(Reg(R8), tup_address);
   ISub(Reg(R8), Const(1L)); (* convert from snake val address -> machine address *)
   IMov(Reg(R8), RegOffset(0, R8)); (* load the tup length into RAX *)
   ICmp(Reg(RAX), Reg(R8));
   IJge(Label(err_lbl));
  ]


let compile_fun_prelude (fun_name : string) : instruction list =
  [
    ILabel(fun_name);
    IPush(Reg(RBP));
    IMov(Reg(RBP), Reg(RSP));

  ]

let compile_fun_postlude : instruction list =
  [
    IMov(Reg(RSP), Reg(RBP));  (* Move stack to how it was at start of this function *)
    IPop(Reg(RBP));
    IRet;
  ]

let rec push_free_vars_from_closure (cur_idx : int) (num_free_vars : int): instruction list =
  if cur_idx >= (num_free_vars)
  then []
  else IPush(Sized(QWORD_PTR, RegOffset((3 + cur_idx) * word_size, RAX))) :: (push_free_vars_from_closure (cur_idx + 1) num_free_vars)
;;

(* shift the RegOffset "stack_idx_shift" SLOTS down the stack (ie. "stack_idx_shift * word_size" bytes) *)
let add_stack_offset (stack_idx_shift : int) (orig : arg) : arg =
  match orig with
  | RegOffset(orig_offset, orig_reg) -> RegOffset(orig_offset - (stack_idx_shift * word_size), orig_reg)
  | _ -> raise (InternalCompilerError "Unexpected env entry for stack offset adjustment")
;;
let rec compile_aexpr (e : tag aexpr) (stack_offset : int) (env : arg envt) : instruction list =
  match e with
  | ALet(id, bind, body, _) ->
    let compiled_bind = compile_cexpr bind stack_offset env in
    let new_dest = add_stack_offset stack_offset (find env id) in
    let new_env = (id, new_dest) :: env in
    let compiled_body = compile_aexpr body stack_offset new_env in
    [ILineComment(sprintf "Let_%s" id)]
    @ compiled_bind
    @ [IMov((find new_env id), Reg(RAX))]
    @ compiled_body
  | ACExpr(expr) -> (compile_cexpr expr stack_offset env)
  | ASeq(left, right, tag) ->
    let seq_left_txt = sprintf "seq_left_%d" tag in
    let seq_right_txt = sprintf "seq_right_%d" tag in
    let compiled_left = (compile_cexpr left stack_offset env) in
    let compiled_right = (compile_aexpr right stack_offset env) in
    [ILineComment(seq_left_txt)]
    @ compiled_left
    @ [ILineComment(seq_right_txt)]
    @ compiled_right
  | ALetRec(bindings, body, tag) ->
    let compiled_bindings =
      List.fold_left (fun cb_acc (name, bound_body) ->
                       let dest = add_stack_offset stack_offset (find env name) in
                         (compile_cexpr bound_body stack_offset env) @ [IMov(dest, Reg(RAX))] @ cb_acc)
                       []
                       bindings in
    [ILineComment(sprintf "LetRec$%d" tag)]
    @ compiled_bindings
    @ (compile_aexpr body stack_offset env)
and compile_cexpr (e : tag cexpr) (stack_offset : int) (env : arg envt) =
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
     @ [IJz(Label(lbl_els))]

     @ [ILabel(lbl_thn)]
     @ (compile_aexpr thn stack_offset env)
     @ [IJmp(Label(lbl_done))]

     @ [ILabel(lbl_els)]
     @ (compile_aexpr els stack_offset env)
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
     @ [IJz(Label(lbl_els))]

     @ [ILabel(lbl_thn)]
     (* LHS is compiled before RHS, so definitely not tail position *)
     @ (compile_aexpr thn stack_offset env)
     @ [IJmp(Label(lbl_done))]

     @ [ILabel(lbl_els)]
     (* Since we check that result is bool, RHS is also not in tail position *)
     @ (compile_aexpr els stack_offset env)
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
        | Print -> [IMov(Reg(RDI), body_imm); ICall(Label("print"));]
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
           IJz(Label(true_lbl));
           (* case not bool *)
           ILabel(false_lbl);
           IMov(Reg(RAX), const_false);
           IJmp(Label(done_lbl));
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
           IJz(Label(true_lbl));
           (* case not num *)
           ILabel(false_lbl);
           IMov(Reg(RAX), const_false);
           IJmp(Label(done_lbl));
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
            (* TODO Lerner provided this *)
            raise (NotYetImplemented "PrintStack not yet implemented")
        | IsTuple ->
          let true_lbl = sprintf "is_tup_true_%d" tag in
          let false_lbl = sprintf "is_tup_false_%d" tag in
          let done_lbl = sprintf "is_tup_done_%d" tag in
          [
           IMov(Reg(RAX), body_imm);
           (* Don't need to save RAX on the stack because we overwrite the
            * value with true/false later. R8 used because And, Cmp don't support imm64 *)
           IMov(Reg(R8), HexConst(tuple_tag_mask));
           IAnd(Reg(RAX), Reg(R8));
           IMov(Reg(R8), HexConst(tuple_tag));
           ICmp(Reg(RAX), Reg(R8));
           IJz(Label(true_lbl));
           (* case not tup *)
           ILabel(false_lbl);
           IMov(Reg(RAX), const_false);
           IJmp(Label(done_lbl));
           (* case is a tup *)
           ILabel(true_lbl);
           IMov(Reg(RAX), const_true);
           (* done *)
           ILabel(done_lbl);
          ]
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
         @ [IJg(Label(lbl_done))]

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
         @ [IJge(Label(lbl_done))]

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
         @ [IJl(Label(lbl_done))]

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
         @ [IJle(Label(lbl_done))]

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
         @ [IJe(Label(lbl_done))]

         @ [ILabel(lbl_false)]
         @ [IMov(Reg(RAX), const_false)]

         @ [ILabel(lbl_done)]
     end
  | CLambda(params, body, tag) ->
    let arity = List.length params in
    let closure_lbl = sprintf "closure$%d" tag in
    let closure_done_lbl = sprintf "closure_done$%d" tag in
    let num_body_vars = (deepest_stack body env) in
    let free_vars_list = List.sort String.compare (free_vars (ACExpr(e))) in
    let num_free_vars = List.length free_vars_list in
    let add_free_vars_to_closure =
      List.flatten (List.mapi (fun idx fv ->
                 [
                 (* Use incoming env here, because it is the env that the lambda is in *)
                 IMov(Reg(scratch_reg), (find env fv));
                 IMov(Sized(QWORD_PTR, RegOffset((3 + idx)*word_size, heap_reg)), Reg(scratch_reg));
                 ])
                free_vars_list) in
    let prelude = compile_fun_prelude closure_lbl in
    (* Trick, we know the env is a list and lookups will return 1st found, so just add the updated values to the front.
       This new env assumes we have pushed all the closed over values to the stack in order.*)
    let new_env = (List.mapi (fun idx fv -> (fv, RegOffset(~-1 * (1 + idx)*word_size, RBP))) free_vars_list) @ env in
    let compiled_body = compile_aexpr body num_free_vars new_env in
    let postlude = compile_fun_postlude in
    let true_heap_size = 3 + num_free_vars in
    let reserved_heap_size = true_heap_size + (true_heap_size mod 2) in
    [IJmp(Label(closure_done_lbl))]
    @ prelude
    @ [IMov(Reg(RAX), RegOffset(2*word_size, RBP))]
    (* Now RAX has the (tagged) func value *)
    @ [
      ISub(Reg(RAX), HexConst(closure_tag)); (* now RAX is heap addr to closure *)
      ]
    @ (push_free_vars_from_closure 0 num_free_vars)
    @ [    (* Don't use temp register here because we assume the RHS will never be very big *)
      ISub(Reg(RSP), Const(Int64.of_int (word_size * num_body_vars)))  (* allocates stack space for all local vars *)]
    @ compiled_body
    @ postlude
    @ [
      ILabel(closure_done_lbl);
      IMov(Sized(QWORD_PTR, RegOffset(0*word_size, heap_reg)), Const(Int64.of_int arity));
      IMov(Sized(QWORD_PTR, RegOffset(1*word_size, heap_reg)), Label(closure_lbl));
      IMov(Sized(QWORD_PTR, RegOffset(2*word_size, heap_reg)), Const(Int64.of_int num_free_vars));
      ]
    @ add_free_vars_to_closure
    @ [
      IMov(Reg(RAX), Reg(heap_reg));
      IAdd(Reg(RAX), HexConst(closure_tag));
      IAdd(Reg(heap_reg), Const(Int64.of_int (reserved_heap_size*word_size)));
      ]
  | CApp(func, args, ct, tag) ->
    let num_args = (List.length args) in
    (* we add 1 below because we will also push the closure itself before making the call *)
    let needs_padding = (num_args + 1) mod 2 == 1 in
    let padding = (if needs_padding then [IMov(Reg(R8), HexConst(0xF0F0F0F0L)); IPush(Reg(R8))] else []) in
    let num_pushes = num_args + 1 (* the closure *) + (if needs_padding then 1 else 0) in
    let args_rev = List.rev args in
    let compiled_func = compile_imm func env in
    begin match ct with
    | Snake ->
        (* TODO- figure out how I will support equal(), print(), etc. *)
        (* Push the args onto stack in reverse order *)
        let push_compiled_args = List.fold_left
                       (fun accum_instrs arg ->
                          let compiled_imm = (compile_imm arg env) in
                          (* Use temp register because can't push imm64 directly *)
                          accum_instrs @ [IMov(Reg(R8), compiled_imm);
                                          IPush(Sized(QWORD_PTR, Reg(R8)))])
                       []
                       args_rev
                       in
        let check_rax_for_closure =
        [ILineComment("check_rax_for_closure (err_CALL_NOT_CLOSURE)");
         IMov(Reg(R9), HexConst(closure_tag_mask));
         IAnd(Reg(RAX), Reg(R9));
         IMov(Reg(R9), HexConst(closure_tag));
         ICmp(Reg(RAX), Reg(R9));
         IJne(Label("err_CALL_NOT_CLOSURE"));] in
        let check_closure_for_arity =
        [ILineComment("check_closure_for_arity (err_CALL_ARITY_ERR)");
         (* RAX is tagged ptr to closure on heap *)
         IMov(Reg(RAX), compiled_func);
         ISub(Reg(RAX), HexConst(closure_tag)); (* now RAX is heap addr to closure *)
         IMov(Reg(RAX), RegOffset(0,RAX)); (* get the arity (machine int) *)
         ICmp(Reg(RAX), Const(Int64.of_int num_args)); (* no temp reg, assume won't have that many args *)
         IJne(Label("err_CALL_ARITY_ERR"));] in
        let padded_comp_args = padding @ push_compiled_args in
        [IMov(Reg(RAX), compiled_func);]
        @ check_rax_for_closure
        @ check_closure_for_arity
        @ padded_comp_args
        @ [
          IMov(Reg(RAX), compiled_func);
          IPush(Reg(RAX)); (*Push the tagged func itself onto the stack*)
          ISub(Reg(RAX), HexConst(closure_tag)); (* now RAX is heap addr to closure *)
          IMov(Reg(RAX), RegOffset(1*word_size,RAX)); (* get the code ptr (machine addr) *)
          ICall(Reg(RAX));
          (* Don't use temp register here because we assume the RHS will never be very big *)
          IAdd(Reg(RSP), Const(Int64.of_int (word_size * num_pushes)));
          ]
    | _ -> raise (InternalCompilerError "(code gen) Unsupported function application call type")
    end
  | CImmExpr(expr) -> [IMov(Reg(RAX), (compile_imm expr env))]
  | CTuple(elems, _) -> 
      let tup_size = List.length elems in
      let need_padding = tup_size mod 2 == 1 in
      let padding_val = HexConst(0xF0F0F0F0L) in
      let padding =
        if need_padding then []
        else
          let offs = tup_size + 1 in
          [IMov(Reg(R8), padding_val); IMov(RegOffset(offs*word_size, R15), Reg(R8))] in
      let next_heap_loc = tup_size + 1 + ((1+tup_size) mod 2) in

      (* store the tuple size on the heap *)
      [IMov(Reg(R8), Const(Int64.of_int tup_size)); IMov(RegOffset(0, R15), Reg(R8))]
      (* store each tuple element on the heap *)
      @ List.flatten
          (List.mapi
            (fun i e ->
              let arg = compile_imm e env in
              let offs = i + 1 in
              [IMov(Reg(R8), arg); IMov(RegOffset(offs*word_size, R15), Reg(R8))])
            elems)
      @ padding
      (* return the pointer to the tuple, make it a snakeval *)
      @ [IMov(Reg(RAX), Reg(R15)); IAdd(Reg(RAX), Const(1L))]
      (* increment the heap ptr *)
      @ [IMov(Reg(R8), Const(Int64.of_int (next_heap_loc * word_size))); IAdd(Reg(R15), Reg(R8))]
  | CGetItem(tup, i, _) ->
      let tup_address = compile_imm tup env in
      let idx = compile_imm i env in

      (* first, do runtime error checking *)
      [IMov(Reg(RAX), tup_address)] (* move tuple address (snakeval) into RAX *)
      @ (check_rax_for_tup "err_GET_NOT_TUPLE")
      @ (check_rax_for_nil "err_NIL_DEREF")
      @ [IMov(Reg(RAX), idx)] (* move the idx (snakeval) into RAX *)
      @ (check_rax_for_num "err_TUP_IDX_NOT_NUM")
      @ [ISar(Reg(RAX), Const(1L))] (* convert from snakeval -> int *)
      @ (check_rax_for_tup_smaller "err_GET_LOW_INDEX")
      @ (check_rax_for_tup_bigger tup_address "err_GET_HIGH_INDEX")

      (* passed checks, now do actual 'get' *)
      @ [IMov(Reg(RAX), tup_address)] (* move tuple address back into RAX *)
      @ [ISub(Reg(RAX), Const(1L))] (* convert from snake val address -> machine address *)
      @ [IMov(Reg(R8), idx)] (* move the idx (snakeval) into R8 *)
      @ [ISar(Reg(R8), Const(1L))] (* convert from snake val -> int *)
      @ [IAdd(Reg(R8), Const(1L))] (* add 1 to the offset to bypass the tup size *)
      @ [IMov(Reg(RAX), RegOffsetReg(RAX,R8,word_size,0))]
  | CSetItem(tup, i, r, _) ->
      let tup_address = compile_imm tup env in
      let idx = compile_imm i env in
      let rhs = compile_imm r env in

      (* first, do runtime error checking *)
      [IMov(Reg(RAX), tup_address)] (* move tuple address (snakeval) into RAX *)
      @ (check_rax_for_tup "err_GET_NOT_TUPLE")
      @ (check_rax_for_nil "err_NIL_DEREF")
      @ [IMov(Reg(RAX), idx)] (* move the idx (snakeval) into RAX *)
      @ (check_rax_for_num "err_TUP_IDX_NOT_NUM")
      @ [ISar(Reg(RAX), Const(1L))] (* convert from snakeval -> int *)
      @ (check_rax_for_tup_smaller "err_GET_LOW_INDEX")
      @ (check_rax_for_tup_bigger tup_address "err_GET_HIGH_INDEX")

      (* passed checks, now do actual 'set' *)
      @ [IMov(Reg(RAX), tup_address)] (* move tuple address (snakeval) into RAX *)
      @ [ISub(Reg(RAX), Const(1L))] (* convert from snake val -> address *)
      @ [IMov(Reg(R8), idx)] (* move the idx (* snakeval *) into R8 *)
      @ [ISar(Reg(R8), Const(1L))] (* convert from snake val -> int *)
      @ [IAdd(Reg(R8), Const(1L))] (* add 1 to the offset to bypass the tup size *)
      @ [IMov(Reg(R11), rhs)]
      @ [IMov(RegOffsetReg(RAX,R8,word_size,0), Reg(R11))]
      @ [IAdd(Reg(RAX), Const(1L))] (* convert the tuple address back to a snakeval *)
and compile_imm e (env : arg envt) : arg =
  match e with
  | ImmNum(n, _) -> Const(Int64.shift_left n 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)
  | ImmNil(_) -> const_nil


let compile_prog ((anfed : tag aprogram), (env : arg envt)) : string =
  match anfed with
  | AProgram(body, _) ->
      let heap_start = [
          ILineComment("heap start");
          IInstrComment(IMov(Reg(heap_reg), Reg(List.nth first_six_args_registers 0)), "Load heap_reg with our argument, the heap pointer");
          IInstrComment(IAdd(Reg(heap_reg), Const(15L)), "Align it to the nearest multiple of 16");
          IInstrComment(IAnd(Reg(heap_reg), HexConst(0xFFFFFFFFFFFFFFF0L)), "by adding no more than 15 to it")
        ] in
      let num_prog_body_vars = (deepest_stack body env) in
      let compiled_body = (compile_aexpr body 0 env) in
      let prelude =
        "section .text
extern error
extern print
extern cinput
extern cequal
global our_code_starts_here" in
      let stack_setup = (compile_fun_prelude "our_code_starts_here") in
      let postlude =
      [ILabel("program_done");]
      @ compile_fun_postlude
      @ [ (* Error Labels *)
          ILabel("err_COMP_NOT_NUM");
          IMov(Reg(RDI), Const(err_COMP_NOT_NUM));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_ARITH_NOT_NUM");
          IMov(Reg(RDI), Const(err_ARITH_NOT_NUM));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_LOGIC_NOT_BOOL");
          IMov(Reg(RDI), Const(err_LOGIC_NOT_BOOL));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_IF_NOT_BOOL");
          IMov(Reg(RDI), Const(err_IF_NOT_BOOL));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_OVERFLOW");
          IMov(Reg(RDI), Const(err_OVERFLOW));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_GET_NOT_TUPLE");
          IMov(Reg(RDI), Const(err_GET_NOT_TUPLE));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_GET_LOW_INDEX");
          IMov(Reg(RDI), Const(err_GET_LOW_INDEX));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_GET_HIGH_INDEX");
          IMov(Reg(RDI), Const(err_GET_HIGH_INDEX));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_GET_NOT_NUM");
          IMov(Reg(RDI), Const(err_GET_NOT_NUM));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_NIL_DEREF");
          IMov(Reg(RDI), Const(err_NIL_DEREF));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_OUT_OF_MEMORY");
          IMov(Reg(RDI), Const(err_OUT_OF_MEMORY));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_SET_NOT_TUPLE");
          IMov(Reg(RDI), Const(err_SET_NOT_TUPLE));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_SET_LOW_INDEX");
          IMov(Reg(RDI), Const(err_SET_LOW_INDEX));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_SET_NOT_NUM");
          IMov(Reg(RDI), Const(err_SET_NOT_NUM));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_SET_HIGH_INDEX");
          IMov(Reg(RDI), Const(err_SET_HIGH_INDEX));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_CALL_NOT_CLOSURE");
          IMov(Reg(RDI), Const(err_CALL_NOT_CLOSURE));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_CALL_ARITY_ERR");
          IMov(Reg(RDI), Const(err_CALL_ARITY_ERR));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_BAD_INPUT");
          IMov(Reg(RDI), Const(err_BAD_INPUT));
          ICall(Label("error"));
          IJmp(Label("program_done"));

          ILabel("err_TUP_IDX_NOT_NUM");
          IMov(Reg(RDI), Const(err_TUP_IDX_NOT_NUM));
          ICall(Label("error"));
          IJmp(Label("program_done"));
        ] in
      let body_assembly_string =
      (to_asm (stack_setup @
      [(* Don't use temp register here because we assume the RHS will never be very big *)
       ISub(Reg(RSP), Const(Int64.of_int (word_size * num_prog_body_vars)))  (* allocates stack space for all local vars *)]
      @ heap_start @ compiled_body @ postlude)) in
      sprintf "%s%s\n" prelude body_assembly_string


let run_if should_run f =
  if should_run then f else no_op_phase
;;

(* We chose to put the desugar phase after the well_formed check to make sure we spit
 * out the correct error location for ill-formed programs.  We choose to desugar before
 * ANFing because the desugar phase is not guaranteed to perform ANFing, therefore we
 * would need to call ANF a second time if we desugared after ANFing.  Tagging and
 * renaming needs to happen before ANFing, so we desugar before these two phases because
 * desugaring would invalidate both tagging and renaming.  Note: tagging and renaming
 * is not a prerequisite to desugaring.
 * *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  (* Invariant: EScIf is not part of the AST *)
  |> (add_phase desugared desugar)
    (* Invariants:
    * 1. EPrim2's should never have "and" or "or" operators
    * 2. Every decl should be desugared into ELetRecs - ie. no Decls left
    * 3. ELet's will never have BTuple's in the receiving position (the lhs).
    * 4. The binds (arguments) to each DFun will never be an BTuple.
    * 5. There will be no ESeq's in our AST.
    * *)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename_and_tag)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase locate_bindings naive_stack_allocation)
  |> (add_phase result compile_prog)
;;
