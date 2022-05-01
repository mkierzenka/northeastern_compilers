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
open Register_allocation
open Util

let err_comp_not_num_lbl     = "?err_comp_not_num"
let err_arith_not_num_lbl    = "?err_arith_not_num"
let err_logic_not_bool_lbl   = "?err_logic_not_bool"
let err_if_not_bool_lbl      = "?err_if_not_bool"
let err_overflow_lbl         = "?err_overflow"
let err_get_not_tuple_lbl    = "?err_get_not_tuple"
let err_get_low_index_lbl    = "?err_get_low_index"
let err_get_high_index_lbl   = "?err_get_high_index"
let err_nil_deref_lbl        = "?err_nil_deref"
let err_out_of_memory_lbl    = "?err_out_of_memory"
let err_set_not_tuple_lbl    = "?err_set_not_tuple"
let err_set_low_index_lbl    = "?err_set_low_index"
let err_set_high_index_lbl   = "?err_set_high_index"
let err_call_not_closure_lbl = "?err_call_not_closure"
let err_call_arity_err_lbl   = "?err_call_arity_err"
let err_get_not_num_lbl      = "?err_get_not_num"
let err_set_not_num_lbl      = "?err_set_not_num"
let err_bad_input_lbl        = "?err_bad_input"

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
let err_NIL_DEREF        = 9L
let err_OUT_OF_MEMORY    = 10L
let err_SET_NOT_TUPLE    = 11L
let err_SET_LOW_INDEX    = 12L
let err_SET_HIGH_INDEX   = 13L
let err_CALL_NOT_CLOSURE = 14L
let err_CALL_ARITY_ERR   = 15L
let err_GET_NOT_NUM      = 16L
let err_SET_NOT_NUM      = 17L
let err_BAD_INPUT        = 18L

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]
let heap_reg = R15
let scratch_reg = R11
let scratch_reg_2 = R12

let print_env env how =
  debug_printf "Env is\n";
  List.iter (fun (id, bind) -> debug_printf "  %s -> %s\n" id (how bind)) env;;

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
    | _ -> 0
  in helpA e

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))

let rec find_dup (l : 'a list) : 'a option =
  match l with
    | [] -> None
    | [x] -> None
    | x::xs ->
      if find_one xs x then Some(x) else find_dup xs
;;

(* Combines two name_envts into one, preferring the first one *)
let prepend env1 env2 =
  let rec help env1 env2 =
    match env1 with
    | [] -> env2
    | ((k, _) as fst)::rst ->
      let rst_prepend = help rst env2 in
      if List.mem_assoc k env2 then rst_prepend else fst::rst_prepend
  in
  help env1 env2

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
    | _ -> 0
  in helpA e

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))

let rec reserve size tag =
  let ok = sprintf "$memcheck_%d" tag in
  [
    IInstrComment(IMov(Reg(RAX), LabelContents("?HEAP_END")),
                 sprintf "Reserving %d words" (size / word_size));
    ISub(Reg(RAX), Const(Int64.of_int size));
    ICmp(Reg(RAX), Reg(heap_reg));
    IJge(Label ok);
  ]
  @ (native_call (Label "?try_gc") [
         (Sized(QWORD_PTR, Reg(heap_reg))); (* alloc_ptr in C *)
         (Sized(QWORD_PTR, Const(Int64.of_int size))); (* bytes_needed in C *)
         (Sized(QWORD_PTR, Reg(RBP))); (* first_frame in C *)
         (Sized(QWORD_PTR, Reg(RSP))); (* stack_top in C *)
    ])
  @ [
      IInstrComment(IMov(Reg(heap_reg), Reg(RAX)), "assume gc success if returning here, so RAX holds the new heap_reg value");
      ILabel(ok);
    ]
and args_help args regs =
  match args, regs with
  | arg :: args, reg :: regs ->
    IMov(Sized(QWORD_PTR, Reg(reg)), arg) :: args_help args regs
  | args, [] ->
    List.rev_map (fun arg -> IPush arg) args
  | [], _ -> []
and native_call label args =
  (* We know that on entry to every function, RSP is 16-byte aligned.
     We know that every frame is a multiple of 16 bytes.
     The call instruction pushes one return pointer onto the stack.
     The first thing we do is push RBP onto the stack
     So, we add 8 bytes of padding IFF the number of spilled args is *ODD*.
  *)
  let num_stack_args = max (List.length args - 6) 0 in
  let padding_needed = (num_stack_args mod 2) <> 0 in
  let setup = (if padding_needed
               then [IInstrComment(IPush(Sized(QWORD_PTR, Const(0L))), "Padding to 16-byte alignment")]
               else []) @ args_help args first_six_args_registers in
  let teardown =
    (if num_stack_args = 0 then []
     else [ IInstrComment(IAdd(Reg(RSP), Const(Int64.of_int(word_size * num_stack_args))),
                          sprintf "Popping %d arguments" num_stack_args) ])
    @ (if padding_needed then [IInstrComment(IAdd(Reg(RSP), Const(Int64.of_int word_size)), "Unpadding one word")]
       else []) in
  setup @ [ ICall(label) ] @ teardown

                                          
(* UPDATE THIS TO HANDLE FIRST-CLASS FUNCTIONS AS NEEDED -- THIS CODE WILL NOT WORK AS WRITTEN *)
and call (closure : arg) args =
  let setup = List.rev_map (fun arg ->
                  match arg with
                  | Sized _ -> IPush(arg)
                  | _ -> IPush(Sized(DWORD_PTR, arg))) args in
  let teardown =
    let len = List.length args in
    if len = 0 then []
    else [ IInstrComment(IAdd(Reg(RSP), Const(Int64.of_int(word_size * len))), sprintf "Popping %d arguments" len) ] in
  setup @ [ ICall(closure) ] @ teardown

(* Compiled Type Checking *)
let check_rax_for_num (err_lbl : string) : instruction list =
  [
   (* This "test" trick depends on num_tag being 0. Scratch reg used because Test doesn't support imm64 *)
   ILineComment("check_rax_for_num (" ^ err_lbl ^ ")");
   IMov(Reg(scratch_reg), HexConst(num_tag_mask));
   ITest(Reg(RAX), Reg(scratch_reg));
   IJnz(Label(err_lbl));
  ]

let check_rax_for_bool (err_lbl : string) : instruction list =
  [
   (* Operate on scratch register instead of RAX. This is because we call AND
    * on the register, which will alter the value. We want to preserve the value
    * in RAX, hence we operate on scratch reg instead. 2nd scratch reg is used
    * as intermediate because And, Cmp don't work on imm64s *)
   ILineComment("check_rax_for_bool (" ^ err_lbl ^ ")");
   IMov(Reg(scratch_reg), Reg(RAX));
   IMov(Reg(scratch_reg_2), HexConst(bool_tag_mask));
   IAnd(Reg(scratch_reg), Reg(scratch_reg_2));
   IMov(Reg(scratch_reg_2), HexConst(bool_tag));
   ICmp(Reg(scratch_reg), Reg(scratch_reg_2));
   IJnz(Label(err_lbl));
  ]

let check_for_overflow = [IJo(Label(err_overflow_lbl))]


let check_rax_for_tup (err_lbl : string) : instruction list =
  [
   (* Operate on scratch register instead of RAX. This is because we call AND
    * on the register, which will alter the value. We want to preserve the value
    * in RAX, hence we operate on scratch reg instead. 2nd scratch reg is used
    * as intermediate because And, Cmp don't work on imm64s *)
   ILineComment("check_rax_for_tup (" ^ err_lbl ^ ")");
   IMov(Reg(scratch_reg), Reg(RAX));
   IMov(Reg(scratch_reg_2), HexConst(tuple_tag_mask));
   IAnd(Reg(scratch_reg), Reg(scratch_reg_2));
   IMov(Reg(scratch_reg_2), HexConst(tuple_tag));
   ICmp(Reg(scratch_reg), Reg(scratch_reg_2));
   IJne(Label(err_lbl));
  ]

let check_rax_for_nil (err_lbl : string) : instruction list =
  [
   ILineComment("check_rax_for_nil (" ^ err_lbl ^ ")");
   IMov(Reg(scratch_reg), const_nil);
   ICmp(Reg(RAX), Reg(scratch_reg));
   IJe(Label(err_lbl));
  ]


(* RAX should be the snakeval of the index (in a tuple)*)
(* DO NOT MODIFY RAX *)
let check_rax_for_tup_smaller (err_lbl : string) : instruction list =
  [
   ILineComment("check_rax_for_tup_smaller (" ^ err_lbl ^ ")");
   ICmp(Reg(RAX), Const(0L));
   (* no scratch register because imm32 0 will be "sign-extended to imm64", which should still be 0 *)
   IJl(Label(err_lbl));
  ]


(* RAX should be the snakeval of the index (in a tuple)*)
(* DO NOT MODIFY RAX *)
let check_rax_for_tup_bigger (tup_address : arg) (err_lbl : string) : instruction list =
  [
   (* Scratch reg is used as intermediate because Cmp don't work on imm64s *)
   ILineComment("check_rax_for_tup_bigger (" ^ err_lbl ^ ")");
   IMov(Reg(scratch_reg), tup_address);
   ISub(Reg(scratch_reg), Const(1L)); (* convert from snake val address -> machine address *)
   IMov(Reg(scratch_reg), RegOffset(0, scratch_reg)); (* load the tup length into RAX *)
   ICmp(Reg(RAX), Reg(scratch_reg));
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

let rec compile_aexpr (e : tag aexpr) (curr_env_name : string) (env : arg name_envt name_envt) (field_nums : int name_envt) : instruction list =
  let sub_env = (find env curr_env_name) in
  match e with
  | ALet(id, bind, body, _) ->
    let compiled_bind =
      match bind with
      | CLambda(params, lambda_body, tag) -> (compile_clambda id params lambda_body tag sub_env env field_nums)
      | _ -> (compile_cexpr bind curr_env_name env field_nums)
      in
    let compiled_body = compile_aexpr body curr_env_name env field_nums in
    [ILineComment(sprintf "Let_%s" id)]
    @ compiled_bind
    @ [IMov((find sub_env id), Reg(RAX))]
    @ compiled_body
  | ACExpr(expr) -> (compile_cexpr expr curr_env_name env field_nums)
  | ASeq(left, right, tag) -> raise (InternalCompilerError "ASeqs should currently be desugared away")
  | ALetRec(bindings, body, tag) ->
    let compiled_bindings =
      List.fold_left (
        fun cb_acc (name, bound_body) ->
          match bound_body with
          | CLambda(params, body, tag) -> (compile_clambda name params body tag sub_env env field_nums) @ cb_acc
          | _ -> raise (InternalCompilerError "LetRecs cannot have non-CLambda bindings")
      ) [] bindings in
    let bound_names = List.map (fun (name, _) -> name) bindings in
    let second_pass =
      let reducer acc (name, body) =
        let abody = ACExpr(body) in
        let fvs = List.sort String.compare (free_vars abody) in
        let locs = List.mapi (fun idx name -> (idx, name)) fvs in
        let fv_lambdas = List.filter (fun (idx, name) -> find_one bound_names name) locs in
        let this_lambda_loc = find sub_env name in
        acc @ List.fold_left (
          fun code_acc (lambda_fv_offset, lambda) ->
          let lambda_ptr_stack_loc = find sub_env lambda in
          code_acc @ [
            IMov(Reg(scratch_reg_2), lambda_ptr_stack_loc); (* Now the free lambda ptr is in scratch reg 2 *)
            IMov(RegOffset((3 + lambda_fv_offset) * word_size, scratch_reg), Reg(scratch_reg_2)); (* Offset of 3 because of closure structure *)
          ]
        ) [
            (* Move lambda location into scratch reg and untag pointer *)
            IMov(Reg(scratch_reg), this_lambda_loc);
            ISub(Reg(scratch_reg), HexConst(closure_tag));
        ] fv_lambdas in
      List.fold_left reducer [] bindings in

    [ILineComment(sprintf "LetRec$%d" tag)]
    @ compiled_bindings
    @ [ILineComment(sprintf "LetRec$%d patching with ptrs to mutually rec closures" tag)]
    @ second_pass
    @ (compile_aexpr body curr_env_name env field_nums)
and compile_clambda (name : string) (params : string list) (lambda_body : tag aexpr) (tag : tag) (sub_env : arg name_envt) (env : arg name_envt name_envt) (field_nums : int name_envt) : instruction list = 
  let arity = List.length params in
  let closure_lbl = name in
  let closure_done_lbl = sprintf "%s_done" name in
  let free_vars_list = List.sort String.compare (free_vars (ACExpr(CLambda(params, lambda_body, tag)))) in
  let num_free_vars = List.length free_vars_list in
  let add_free_vars_to_closure =
    List.flatten (List.mapi (fun idx fv ->
              [
              (* Use incoming env here, because it is the env that actually has the free var values *)
              IMov(Reg(scratch_reg), (find sub_env fv));
              IMov(Sized(QWORD_PTR, RegOffset((3 + idx) * word_size, heap_reg)), Reg(scratch_reg));
              ])
              free_vars_list) in
  let true_heap_size = 3 + num_free_vars in
  let reserved_heap_size = true_heap_size + (true_heap_size mod 2) in
  let (prelude, lambda_body, postlude) = compile_fun closure_lbl params lambda_body env free_vars_list field_nums in
  [IJmp(Label(closure_done_lbl))]
  @ prelude
  @ lambda_body
  @ postlude
  @ [
    ILabel(closure_done_lbl);
    IMov(Sized(QWORD_PTR, RegOffset(0 * word_size, heap_reg)), Const(Int64.of_int arity));
    IMov(Sized(QWORD_PTR, RegOffset(1 * word_size, heap_reg)), Label(closure_lbl));
    IMov(Sized(QWORD_PTR, RegOffset(2 * word_size, heap_reg)), Const(Int64.of_int num_free_vars));
    ]
  @ add_free_vars_to_closure
  @ [
    IMov(Reg(RAX), Reg(heap_reg));
    IAdd(Reg(RAX), HexConst(closure_tag));
    IAdd(Reg(heap_reg), Const(Int64.of_int (reserved_heap_size * word_size)));
    ]
  @ [IMov(find sub_env name, Reg(RAX))]
and compile_cexpr (e : tag cexpr) (curr_env_name : string) (env : arg name_envt name_envt) (field_nums : int name_envt) =
  let sub_env = find env curr_env_name in
  match e with
  | CIf(cond, thn, els, tag) ->
     let cond_reg = compile_imm cond sub_env in
     let lbl_comment = sprintf "if_%d" tag in
     let lbl_thn = sprintf "if_then_%d" tag in
     let lbl_els = sprintf "if_else_%d" tag in
     let lbl_done = sprintf "if_done_%d" tag in
     (* check cond for boolean val *)
     [ILineComment(lbl_comment)]
     @ [IMov(Reg(RAX), cond_reg)]
     @ (check_rax_for_bool err_if_not_bool_lbl) 
     (* test for RAX == true *)
     (* need to use scratch register because Test cannot accept imm64 *)
     @ [IMov(Reg(scratch_reg), bool_mask)]
     @ [ITest(Reg(RAX), Reg(scratch_reg))]
     @ [IJz(Label(lbl_els))]

     @ [ILabel(lbl_thn)]
     @ (compile_aexpr thn curr_env_name env field_nums)
     @ [IJmp(Label(lbl_done))]

     @ [ILabel(lbl_els)]
     @ (compile_aexpr els curr_env_name env field_nums)
     @ [ILabel(lbl_done)]
  | CScIf(cond, thn, els, tag) ->
     let cond_reg = compile_imm cond sub_env in
     let lbl_comment = sprintf "scif_%d" tag in
     let lbl_thn = sprintf "scif_then_%d" tag in
     let lbl_els = sprintf "scif_else_%d" tag in
     let lbl_done = sprintf "scif_done_%d" tag in
     (* check cond for boolean val *)
     [ILineComment(lbl_comment)]
     @ [IMov(Reg(RAX), cond_reg)]
     @ (check_rax_for_bool err_logic_not_bool_lbl)
     (* test for RAX == true *)
     (* need to use scratch register because Test cannot accept imm64 *)
     @ [IMov(Reg(scratch_reg), bool_mask)]
     @ [ITest(Reg(RAX), Reg(scratch_reg))]
     @ [IJz(Label(lbl_els))]

     @ [ILabel(lbl_thn)]
     (* LHS is compiled before RHS, so definitely not tail position *)
     @ (compile_aexpr thn curr_env_name env field_nums)
     @ [IJmp(Label(lbl_done))]

     @ [ILabel(lbl_els)]
     (* Since we check that result is bool, RHS is also not in tail position *)
     @ (compile_aexpr els curr_env_name env field_nums)
     @ (check_rax_for_bool err_logic_not_bool_lbl) 
     @ [ILabel(lbl_done)]
  | CPrim1(op, body, tag) ->
    let body_imm = compile_imm body sub_env in
     begin match op with
       | Add1 ->
           [IMov(Reg(RAX), body_imm)]
           @ (check_rax_for_num err_arith_not_num_lbl) 
           @ [IAdd(Reg(RAX), Const(2L))]
           @ check_for_overflow
       | Sub1 ->
           [IMov(Reg(RAX), body_imm)]
           @ (check_rax_for_num err_arith_not_num_lbl)
           @ [ISub(Reg(RAX), Const(2L))]
           @ check_for_overflow
        | Print -> raise (InternalCompilerError "Print Prim1s should've been desugared away")
        | IsBool ->
          let true_lbl = sprintf "is_bool_true_%d" tag in
          let false_lbl = sprintf "is_bool_false_%d" tag in
          let done_lbl = sprintf "is_bool_done_%d" tag in
          [
           IMov(Reg(RAX), body_imm);
           (* Don't need to save RAX on the stack because we overwrite the
            * value with true/false later. Scratch reg used because And, Cmp don't support imm64 *)
           IMov(Reg(scratch_reg), HexConst(bool_tag_mask));
           IAnd(Reg(RAX), Reg(scratch_reg));
           IMov(Reg(scratch_reg), HexConst(bool_tag));
           ICmp(Reg(RAX), Reg(scratch_reg));
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
           (* This "test" trick depends on num_tag being 0. Scratch reg used because Test doesn't support imm64 *)
           IMov(Reg(scratch_reg), HexConst(num_tag_mask));
           ITest(Reg(RAX), Reg(scratch_reg));
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
           @ (check_rax_for_bool err_logic_not_bool_lbl)
           (* need to use scratch register because Xor cannot accept imm64 *)
           @ [IMov(Reg(scratch_reg), bool_mask)]
           @ [IXor(Reg(RAX), Reg(scratch_reg))]
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
            * value with true/false later. Scratch reg used because And, Cmp don't support imm64 *)
           IMov(Reg(scratch_reg), HexConst(tuple_tag_mask));
           IAnd(Reg(RAX), Reg(scratch_reg));
           IMov(Reg(scratch_reg), HexConst(tuple_tag));
           ICmp(Reg(RAX), Reg(scratch_reg));
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
     let lhs_reg = compile_imm lhs sub_env in
     let rhs_reg = compile_imm rhs sub_env in
     begin match op with
      | Plus ->
         (* check rhs for numerical val *)
         [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_num err_arith_not_num_lbl)
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num err_arith_not_num_lbl)
         (* need to use a scratch register because ADD does not properly handle imm64 (for overflow) *)
         @ [IMov(Reg(scratch_reg), rhs_reg)]
         @ [IAdd(Reg(RAX), Reg(scratch_reg))]
         @ check_for_overflow
      | Minus ->
         (* check rhs for numerical val *)
         [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_num err_arith_not_num_lbl)
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num err_arith_not_num_lbl)
         (* need to use a scratch register because SUB does not properly handle imm64 (for overflow) *)
         @ [IMov(Reg(scratch_reg), rhs_reg)]
         @ [ISub(Reg(RAX), Reg(scratch_reg))]
         @ check_for_overflow
      | Times ->
         (* check rhs for numerical val *)
         [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_num err_arith_not_num_lbl)
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num err_arith_not_num_lbl)
         @ [ISar(Reg(RAX), Const(1L))]
         (* need to use a scratch register because IMUL does not properly handle imm64 (for overflow) *)
         @ [IMov(Reg(scratch_reg), rhs_reg)]
         @ [IMul(Reg(RAX), Reg(scratch_reg))]
         @ check_for_overflow
      | And -> raise (InternalCompilerError "Impossible: 'and' should be rewritten")
      | Or -> raise (InternalCompilerError "Impossible: 'or' should be rewritten")
      | Greater ->
         let lbl_false = sprintf "greater_false_%d" tag in
         let lbl_done = sprintf "greater_done_%d" tag in

         (* check rhs for numerical val *)
         [IMov(Reg(RAX), rhs_reg)]
         @ (check_rax_for_num err_comp_not_num_lbl)
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num err_comp_not_num_lbl)

         (* need to use scratch register because Test cannot accept imm64 *)
         @ [IMov(Reg(scratch_reg), rhs_reg)]
         @ [ICmp(Reg(RAX), Reg(scratch_reg))]
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
         @ (check_rax_for_num err_comp_not_num_lbl)
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num err_comp_not_num_lbl)

         (* need to use scratch register because Test cannot accept imm64 *)
         @ [IMov(Reg(scratch_reg), rhs_reg)]
         @ [ICmp(Reg(RAX), Reg(scratch_reg))]
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
         @ (check_rax_for_num err_comp_not_num_lbl)
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num err_comp_not_num_lbl)

         (* need to use scratch register because Test cannot accept imm64 *)
         @ [IMov(Reg(scratch_reg), rhs_reg)]
         @ [ICmp(Reg(RAX), Reg(scratch_reg))]
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
         @ (check_rax_for_num err_comp_not_num_lbl)
         (* check lhs for numerical val *)
         @ [IMov(Reg(RAX), lhs_reg)]
         @ (check_rax_for_num err_comp_not_num_lbl)

         (* need to use scratch register because Test cannot accept imm64 *)
         @ [IMov(Reg(scratch_reg), rhs_reg)]
         @ [ICmp(Reg(RAX), Reg(scratch_reg))]
         @ [IMov(Reg(RAX), const_true)]
         @ [IJle(Label(lbl_done))]

         @ [ILabel(lbl_false)]
         @ [IMov(Reg(RAX), const_false)]

         @ [ILabel(lbl_done)]
      | Eq ->
         let lbl_false = sprintf "eq_false_%d" tag in
         let lbl_done = sprintf "eq_done_%d" tag in

         [IMov(Reg(RAX), lhs_reg)]

         (* need to use scratch register because Test cannot accept imm64 *)
         @ [IMov(Reg(scratch_reg), rhs_reg)]
         @ [ICmp(Reg(RAX), Reg(scratch_reg))]
         @ [IMov(Reg(RAX), const_true)]
         @ [IJe(Label(lbl_done))]

         @ [ILabel(lbl_false)]
         @ [IMov(Reg(RAX), const_false)]

         @ [ILabel(lbl_done)]
      | CheckSize -> raise (NotYetImplemented "CheckSize not currently used in compilation")
     end
  | CLambda _ -> raise (InternalCompilerError "Unbound CLambdas should have been processed away")
  | CApp(func, args, ct, tag) ->
    let num_args = (List.length args) in
    (* we add 1 below because we will also push the closure itself before making the call *)
    let needs_padding = (num_args + 1) mod 2 == 1 in
    let padding = (if needs_padding then [IMov(Reg(scratch_reg), HexConst(0xF0F0F0F0L)); IPush(Reg(scratch_reg))] else []) in
    let num_pushes = num_args + 1 (* the closure *) + (if needs_padding then 1 else 0) in
    let args_rev = List.rev args in
    let compiled_func = compile_imm func sub_env in
    begin match ct with
    | Snake ->
        (* TODO- figure out how I will support equal(), print(), etc. *)
        (* Push the args onto stack in reverse order *)
        let push_compiled_args = List.fold_left
                       (fun accum_instrs arg ->
                          let compiled_imm = (compile_imm arg sub_env) in
                          (* Use scratch register because can't push imm64 directly *)
                          accum_instrs @ [IMov(Reg(scratch_reg), compiled_imm);
                                          IPush(Sized(QWORD_PTR, Reg(scratch_reg)))])
                       []
                       args_rev
                       in
        let check_rax_for_closure =
        [ILineComment(sprintf "check_rax_for_closure (%s)" err_call_not_closure_lbl);
         IMov(Reg(scratch_reg_2), HexConst(closure_tag_mask));
         IAnd(Reg(RAX), Reg(scratch_reg_2));
         IMov(Reg(scratch_reg_2), HexConst(closure_tag));
         ICmp(Reg(RAX), Reg(scratch_reg_2));
         IJne(Label(err_call_not_closure_lbl));] in
        let check_closure_for_arity =
        [ILineComment(sprintf "check_closure_for_arity (%s)" err_call_arity_err_lbl);
         (* RAX is tagged ptr to closure on heap *)
         IMov(Reg(RAX), compiled_func);
         ISub(Reg(RAX), HexConst(closure_tag)); (* now RAX is heap addr to closure *)
         IMov(Reg(RAX), RegOffset(0,RAX)); (* get the arity (machine int) *)
         ICmp(Reg(RAX), Const(Int64.of_int num_args)); (* no scratch reg, assume won't have that many args *)
         IJne(Label(err_call_arity_err_lbl));] in
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
          (* Don't use scratch register here because we assume the RHS will never be very big *)
          IAdd(Reg(RSP), Const(Int64.of_int (word_size * num_pushes)));
          ]
    | Native ->
    begin
    match func with
    | ImmId(fname, _) ->
      let extern_fname = extern_name fname in
      let compiled_args = if num_args > 6
        then raise (InternalCompilerError "(code gen) Too many args for native function call")
        else List.map (fun arg -> (compile_imm arg sub_env)) args in
      [ILineComment("Native call: " ^ extern_fname ^ (sprintf " (tag: %d)" tag));]
      @ (native_call (Label extern_fname) compiled_args)
    | _ -> raise (InternalCompilerError "(code gen) Unsupported native function expr")
    end
    | _ -> raise (InternalCompilerError "(code gen) Unsupported function application call type")
    end
  | CImmExpr(expr) -> [IMov(Reg(RAX), (compile_imm expr sub_env))]
  | CTuple(elems, _) ->
      let tup_size = List.length elems in
      let need_padding = tup_size mod 2 == 1 in
      let padding_val = HexConst(0xF0F0F0F0L) in
      let padding =
        if need_padding then []
        else
          let offs = tup_size + 1 in
          [IMov(Reg(scratch_reg), padding_val); IMov(RegOffset(offs*word_size, heap_reg), Reg(scratch_reg))] in
      let next_heap_loc = tup_size + 1 + ((1+tup_size) mod 2) in

      (* store the tuple size on the heap *)
      [IMov(Reg(scratch_reg), Const(Int64.of_int tup_size)); IMov(RegOffset(0, heap_reg), Reg(scratch_reg))]
      (* store each tuple element on the heap *)
      @ List.flatten
          (List.mapi
            (fun i e ->
              let arg = compile_imm e sub_env in
              let offs = i + 1 in
              [IMov(Reg(scratch_reg), Sized(QWORD_PTR, arg)); IMov(RegOffset(offs*word_size, heap_reg), Reg(scratch_reg))])
            elems)
      @ padding
      (* return the pointer to the tuple, make it a snakeval *)
      @ [IMov(Reg(RAX), Reg(heap_reg)); IAdd(Reg(RAX), Const(1L))]
      (* increment the heap ptr *)
      @ [IMov(Reg(scratch_reg), Const(Int64.of_int (next_heap_loc * word_size))); IAdd(Reg(heap_reg), Reg(scratch_reg))]
  | CGetItem(tup, i, _) ->
      let tup_address = compile_imm tup sub_env in
      let idx = compile_imm i sub_env in

      (* first, do runtime error checking *)
      [IMov(Reg(RAX), tup_address)] (* move tuple address (snakeval) into RAX *)
      @ (check_rax_for_tup err_get_not_tuple_lbl)
      @ (check_rax_for_nil err_nil_deref_lbl)
      @ [IMov(Reg(RAX), idx)] (* move the idx (snakeval) into RAX *)
      @ (check_rax_for_num err_get_not_num_lbl)
      @ [ISar(Reg(RAX), Const(1L))] (* convert from snakeval -> int *)
      @ (check_rax_for_tup_smaller err_get_low_index_lbl)
      @ (check_rax_for_tup_bigger tup_address err_get_high_index_lbl)

      (* passed checks, now do actual 'get' *)
      @ [IMov(Reg(RAX), tup_address)] (* move tuple address back into RAX *)
      @ [ISub(Reg(RAX), Const(1L))] (* convert from snake val address -> machine address *)
      @ [IMov(Reg(scratch_reg), idx)] (* move the idx (snakeval) into scratch reg *)
      @ [ISar(Reg(scratch_reg), Const(1L))] (* convert from snake val -> int *)
      @ [IAdd(Reg(scratch_reg), Const(1L))] (* add 1 to the offset to bypass the tup size *)
      @ [IMov(Reg(RAX), RegOffsetReg(RAX,scratch_reg,word_size,0))]
  | CSetItem(tup, i, r, _) ->
      let tup_address = compile_imm tup sub_env in
      let idx = compile_imm i sub_env in
      let rhs = compile_imm r sub_env in

      (* first, do runtime error checking *)
      [IMov(Reg(RAX), tup_address)] (* move tuple address (snakeval) into RAX *)
      @ (check_rax_for_tup err_get_not_tuple_lbl)
      @ (check_rax_for_nil err_nil_deref_lbl)
      @ [IMov(Reg(RAX), idx)] (* move the idx (snakeval) into RAX *)
      @ (check_rax_for_num err_set_not_num_lbl)
      @ [ISar(Reg(RAX), Const(1L))] (* convert from snakeval -> int *)
      @ (check_rax_for_tup_smaller err_get_low_index_lbl)
      @ (check_rax_for_tup_bigger tup_address err_get_high_index_lbl)

      (* passed checks, now do actual 'set' *)
      @ [IMov(Reg(RAX), tup_address)] (* move tuple address (snakeval) into RAX *)
      @ [ISub(Reg(RAX), Const(1L))] (* convert from snake val -> address *)
      @ [IMov(Reg(scratch_reg), idx)] (* move the idx (* snakeval *) into scratch reg *)
      @ [ISar(Reg(scratch_reg), Const(1L))] (* convert from snake val -> int *)
      @ [IAdd(Reg(scratch_reg), Const(1L))] (* add 1 to the offset to bypass the tup size *)
      @ [IMov(Reg(scratch_reg_2), rhs)]
      @ [IMov(RegOffsetReg(RAX,scratch_reg,word_size,0), Reg(scratch_reg_2))]
      @ [IAdd(Reg(RAX), Const(1L))] (* convert the tuple address back to a snakeval *)
  | CRecord(binds, _) -> [] (* raise (NotYetImplemented "Records not yet supported") *)
and compile_imm e (sub_env : arg name_envt) : arg =
  match e with
  | ImmNum(n, _) -> Const(Int64.shift_left n 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find sub_env x)
  | ImmNil(_) -> const_nil


(* IMPLEMENT THIS FROM YOUR PREVIOUS ASSIGNMENT *)
(* Additionally, you are provided an initial environment of values that you may want to
   assume should take up the first few stack slots.  See the compiliation of Programs
   below for one way to use this ability... *)

(* Compile a function, returns tuple of prelude,body,postlude *)
and compile_fun (name : string) (params : string list) (body : tag aexpr) (env : arg name_envt name_envt) (free_var_list : string list) (field_nums : int name_envt) :
  (instruction list * instruction list * instruction list) =
    let rec min_slot_addr (sub_env : arg name_envt) : int =
      let get_bytes (arg : arg) : int =
        match arg with RegOffset(bytes, _) -> bytes | _ -> raise (InternalCompilerError "Unexpected arg for get_bytes") in
      match sub_env with
      | (_, addr_arg)::rest ->
        let addr = get_bytes addr_arg in
        let min_addr_rest = min_slot_addr rest in
        if addr < min_addr_rest then addr else min_addr_rest
      | [] -> 0 in
    let sub_env = find env name in
    let load_free_vars = List.flatten (List.mapi (
      fun idx free_var -> [
        IMov(Reg(scratch_reg), RegOffset((3 + idx) * word_size, RAX));
        IMov(find sub_env free_var, Reg(scratch_reg));
      ]
    ) free_var_list) in
    let prelude = compile_fun_prelude name in
    let compiled_body = compile_aexpr body name env field_nums in
    let postlude = compile_fun_postlude in (
      prelude,
      [IMov(Reg(RAX), RegOffset(2 * word_size, RBP))] (* Now RAX has the (tagged) func value *)
      @ [ISub(Reg(RAX), HexConst(closure_tag))] (* now RAX is heap addr to closure *)
      
      (* Don't use scratch register here because we assume the RHS will never be very big *)
      (* allocates stack space for all free and local vars *)
      @ [IAdd(Reg(RSP), Const(Int64.of_int (min_slot_addr sub_env)))]
      @ load_free_vars
      @ compiled_body,
      postlude
    )

(* This function can be used to take the native functions and produce DFuns whose bodies
   simply contain an EApp (with a Native call_type) to that native function.  Then,
   your existing compilation can turn these DFuns into ELambdas, which can then be called
   as in the rest of Fer-De-Lance, but the Native EApps will do the work of actually
   native_calling the runtime-provided functions. *)
let add_native_lambdas (p : sourcespan program) =
  let wrap_native name arity =
    match arity with
    | None -> raise (InternalCompilerError "Bad native lambda")
    | Some a ->
      let argnames = List.init a (fun i -> sprintf "%s_arg_%d" name i) in
      [DFun(name, List.map (fun name -> BName(name, false, dummy_span)) argnames, EApp(EId(name, dummy_span), List.map(fun name -> EId(name, dummy_span)) argnames, Native, dummy_span), dummy_span)]
  in
  match p with
  | Program(declss, body, tag) ->
    Program((List.fold_left (fun declss (name, (_, _, arity)) -> (wrap_native name arity)::declss) declss native_fun_bindings), body, tag)

let compile_prog (anfed, (env : arg name_envt name_envt), (field_nums : int name_envt)) =
  let prelude =
    "section .text
extern ?error
extern ?input
extern ?print
extern ?print_stack
extern ?equal
extern ?try_gc
extern ?HEAP
extern ?HEAP_END
extern ?set_stack_bottom
global ?our_code_starts_here" in
  let field_names_table =
    "section .data\n" ^ (
      if field_nums = []
      then "global ?num_fields\n?num_fields: dd 0\nglobal ?fields\n?fields: db ?"
      else
        (* field_nums looks like [("field_name_1" : str, field_num : int), ("field_name_2" : str, field_num_2 : int)] *)
        (* first, order the list: *)
        let ordered_fields = List.sort (fun (_, i) (_, j) -> i - j) field_nums in
        (* then, for each field in ascending order, generate its lines:
          global ?field_name_x
          ?field_name_x: db `{field name}\000`
        *)
        let labels_and_names = List.map (fun (name, num) -> (sprintf "?field_%s_%d" name num, name)) ordered_fields in
        let lines_per_field = List.map (
          fun (label, name) -> sprintf "global %s\n%s: db '%s', 0" label label name
        ) labels_and_names in
        (* lastly, generate the final lines:
          global ?num_fields
          ?num_fields: dd {number of fields in the program}
          global ?fields
          ?fields: %(?field_name_0, ?field_name_1, ..., ?field_name_n)
        *)
        let final_lines = [
          "global ?num_fields";
          sprintf "?num_fields: dd %d" (List.length field_nums);
          "global ?fields";
          sprintf "?fields: dq %%(%s)" (ExtString.String.join ", " (List.map (fun (l, _) -> l) labels_and_names));
        ] in
        ExtString.String.join "\n" (lines_per_field @ final_lines)
    ) ^ "\n" in
  let suffix = sprintf "
?err_comp_not_num:%s
?err_arith_not_num:%s
?err_logic_not_bool:%s
?err_if_not_bool:%s
?err_overflow:%s
?err_get_not_tuple:%s
?err_get_low_index:%s
?err_get_high_index:%s
?err_nil_deref:%s
?err_out_of_memory:%s
?err_set_not_tuple:%s
?err_set_low_index:%s
?err_set_high_index:%s
?err_call_not_closure:%s
?err_call_arity_err:%s
?err_get_not_num:%s
?err_set_not_num:%s
?err_bad_input:%s
"
                       (to_asm (native_call (Label "?error") [Const(err_COMP_NOT_NUM); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_ARITH_NOT_NUM); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_LOGIC_NOT_BOOL); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_IF_NOT_BOOL); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_OVERFLOW); Reg(RAX)]))
                       (to_asm (native_call (Label "?error") [Const(err_GET_NOT_TUPLE); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_GET_LOW_INDEX); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_GET_HIGH_INDEX)]))
                       (to_asm (native_call (Label "?error") [Const(err_NIL_DEREF); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_OUT_OF_MEMORY); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_SET_NOT_TUPLE); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_SET_LOW_INDEX); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_SET_HIGH_INDEX); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_CALL_NOT_CLOSURE); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_CALL_ARITY_ERR); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_GET_NOT_NUM); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_SET_NOT_NUM); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_BAD_INPUT); Reg(scratch_reg)]))
  in
  match anfed with
  | AProgram(body, _) ->
  (* $heap and $size are mock parameter names, just so that compile_fun knows our_code_starts_here takes in 2 parameters *)
     let (ocsh_prelude, ocsh_body, ocsh_postlude) = compile_fun "?our_code_starts_here" ["$heap"; "$size"] body env [] field_nums in
     let heap_start =
       [
         ILineComment("heap start");
         IInstrComment(IMov(Sized(QWORD_PTR, Reg(heap_reg)), Reg(List.nth first_six_args_registers 0)), "Load heap_reg with our argument, the heap pointer");
         IInstrComment(IAdd(Sized(QWORD_PTR, Reg(heap_reg)), Const(15L)), "Align it to the nearest multiple of 16");
         IMov(Reg scratch_reg, HexConst(0xFFFFFFFFFFFFFFF0L));
         IInstrComment(IAnd(Sized(QWORD_PTR, Reg(heap_reg)), Reg scratch_reg), "by adding no more than 15 to it");
       ] in
     let set_stack_bottom =
       [
         IMov(Reg scratch_reg_2, Reg RDI);
       ]
       @ (native_call (Label "?set_stack_bottom") [Reg(RBP)])
       @ [
           IMov(Reg RDI, Reg scratch_reg_2)
         ] in
     let main = (ocsh_prelude @ set_stack_bottom @ heap_start @ ocsh_body @ ocsh_postlude) in
     sprintf "%s%s%s%s\n" field_names_table prelude (to_asm main) suffix
;;

let run_if should_run f =
  if should_run then f else no_op_phase
;;

let pick_alloc_strategy (strat : alloc_strategy) =
  match strat with
  | Naive -> naive_stack_allocation
  (* | Register -> register_allocation *)
  | Register -> raise (InternalCompilerError "Register allocation not complete")
;;

let compile_to_string ?no_builtins:(no_builtins=false) (alloc_strat : alloc_strategy) (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  |> (run_if (not no_builtins) (add_phase add_natives add_native_lambdas))
  |> (add_phase desugared desugar)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename_and_tag)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase locate_bindings (pick_alloc_strategy alloc_strat))
  |> (add_phase result compile_prog)
;;
