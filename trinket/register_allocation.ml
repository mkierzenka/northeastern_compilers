open Assembly
open Errors
open Exprs
open Graph
open Printf
open Util

let caller_saved_regs : arg list =
  [ Reg RDI
  ; Reg RSI
  ; Reg RDX
  ; Reg RCX
  ; Reg R8
  ; Reg R9
  ; Reg R10
  ]
;;

let callee_saved_regs : arg list =
  [ Reg R12
  ; Reg R14
  ; Reg RBX
  ]
;;


(* IMPLEMENT THE BELOW *)
(* TODO- expand this set. Perhaps can put the x64 calling convention regs into this list. *)
let reg_colors : arg list =
  [
    Reg R10;
    (* Reg R11; scratch_reg *)
    (* Reg R12; scratch_reg_2 *)
    Reg R13;
    Reg R14;
    Reg RBX;
    (* TODO- possible include caller_saved_regs as colors,
    may need to stack push/pop to save though *)
  ]

let rec get_minimum_unused_color (colors : arg list) (nbrs : arg list) : arg =
  match colors with
  | head::tail ->
      begin
      match (List.find_opt ((=) head) nbrs) with
      | (Some(_)) -> get_minimum_unused_color tail nbrs
      | None -> head
      end
  | [] ->
      let descending_reg_offsets =
        List.sort (
          fun nbr1 nbr2 ->
            match (nbr1, nbr2) with
            | (RegOffset(off1, RBP), RegOffset(off2, RBP)) -> off1 - off2 (* descending offset is increasing value because stack direction *)
            | _ -> raise (InternalCompilerError "Registers with same offset allocated")
        ) (List.filter (function (RegOffset(_, RBP)) -> true | _ -> false) nbrs) in
      match (List.hd descending_reg_offsets) with
      | RegOffset(off, RBP) -> RegOffset(off - 8, RBP)
      | _ -> raise (
        InternalCompilerError "RegOffset sorting failed to raise error when encountering non-RegOffset register"
      )

let min_unused_color (nbrs_colors : arg list) : arg =
  let rec min_unused_reg (regs : arg list) (nbrs_colors : arg list) : arg option =
    match regs with
    | reg::rest -> if not (List.mem reg nbrs_colors) then Some(reg) else (min_unused_reg rest nbrs_colors)
    | _ -> None
  and min_unused_reg_offset (curr_offset : int) (nbrs_colors : arg list) : arg =
    match nbrs_colors with
    | RegOffset(found_offset, RBP)::rest -> if found_offset < curr_offset then (min_unused_reg_offset curr_offset rest) else (min_unused_reg_offset (found_offset - word_size) rest)
    | RegOffset(_, _)::rest -> raise (InternalCompilerError "Coloring found offset not from RBP")
    | Reg(_)::rest -> (min_unused_reg_offset curr_offset rest)
    | _ -> RegOffset(curr_offset, RBP)
  in
  match (min_unused_reg reg_colors nbrs_colors) with
  | Some(arg) -> arg
  | None -> (min_unused_reg_offset ~-8 nbrs_colors)

let interfere (e : StringSet.t aexpr) (live : StringSet.t) : grapht =
  let rec interfere_aexpr (e : StringSet.t aexpr) (live : StringSet.t) : grapht =
    match e with
    | ASeq(cexp, aexp, _) -> graph_union (interfere_cexpr cexp live) (interfere_aexpr aexp live)
    | ALet(fname, CLambda(args, body, fvs), let_body, _) -> raise (NotYetImplemented "interference of lambda exprs")
    | ALet(sym, bind, body, _) ->
        let body_fvs = get_tag_A body in
        let body_fvs_without_sym = StringSet.diff body_fvs (StringSet.singleton sym) in
        let bind_conflicts = interfere_cexpr bind live in
        let outer = StringSet.fold (fun body_fv acc -> (add_edge acc sym body_fv)) body_fvs_without_sym empty in
        let body_conflicts = interfere_aexpr body (StringSet.add sym live) in
        let live_conflicts = StringSet.fold (fun neighbor acc -> add_edge acc sym neighbor) live empty in
        graph_union_all [outer; body_conflicts; live_conflicts; bind_conflicts]
    | ALetRec _ -> raise (NotYetImplemented "interference of letrec exprs")
    (* | ALetRec((fname, CLambda(args, body, fvs))::bindings, let_rec_body, let_rec_fvs) ->
    | ALetRec([], body, _) ->
    | ALetRec _ -> raise (InternalCompilerError "LetRecs cannot have non-CLambda bindings") *)
    | ACExpr(cexpr) -> interfere_cexpr cexpr live
  and interfere_cexpr (e : StringSet.t cexpr) (live : StringSet.t) : grapht =
    match e with
    | CIf(_, thn, els, _) -> graph_union (interfere_aexpr thn live) (interfere_aexpr els live)
    | CScIf(_, thn, els, _) -> graph_union (interfere_aexpr thn live) (interfere_aexpr els live)
    | _ -> empty
  in
  interfere_aexpr e live

let color_graph (g: grapht) (init_env: arg name_envt) : arg name_envt =
  (* Create a worklist of nodes ordered by increasing degree (ie. top of stack is min-degree node of graph) *)
  let rec create_worklist (g : grapht) : string list =
    let rec create_worklist_helper (g : grapht) (init_list : string list) : string list =
      (* find node with highest degree *)
      let max_node_and_nbrs_ct = Graph.fold (
        fun node neighbors acc ->
          let node_card = NeighborSet.cardinal neighbors in
            match acc with
            | Some(max_node_so_far, max_card_so_far) -> if node_card > max_card_so_far then Some(node, node_card) else acc
            | None -> Some(node, node_card)
      ) g None in
      match max_node_and_nbrs_ct with
      | Some(max_node, _) -> (create_worklist_helper (remove_node g max_node) (max_node::init_list))
      | None -> init_list in
    create_worklist_helper g [] in
    (* worklist is treated as a stack, first element is node with min degree & last elem is node with max degree *)
  let rec color_worklist (g: grapht) (worklist : string list) (env: arg name_envt) : arg name_envt =
    match worklist with
    | head::rest ->
      let nbrs = (get_neighbors g head) in
      let nbrs_colors = List.fold_left (
        fun colors_so_far nbr ->
          match (find_opt env nbr) with
          | None -> colors_so_far
          | Some(color) -> color :: colors_so_far
      ) [] nbrs in
      (color_worklist g rest ((head, (min_unused_color nbrs_colors))::env))
    | _ -> env in
  let worklist = create_worklist g in
  color_worklist g worklist init_env

let assign_colors_to_aexpr (e : StringSet.t aexpr) (init_env : arg name_envt) : arg name_envt =
  color_graph (interfere e StringSet.empty) init_env

let register_allocation (prog: tag aprogram) : tag aprogram * arg name_envt name_envt =
  let fv_prog = free_vars_cache prog in
  let rec help_aexpr (body : StringSet.t aexpr) (si : int) (curr_env_name : string) (env : arg name_envt name_envt) : arg name_envt name_envt * int =
    let help_closure (fname : string) (args : string list) (closure_body : StringSet.t aexpr) (fvs : StringSet.t) (closure_si : int) (closure_env : arg name_envt name_envt) : arg name_envt name_envt * int =
      let args_with_idx = List.mapi (fun i arg -> (arg, RegOffset((i + 3) * word_size, RBP))) args in
      let new_sub_env = List.fold_left (fun accum_env cell -> cell :: accum_env) [] args_with_idx in
      let new_sub_env_with_self = (fname, RegOffset(2*word_size, RBP)) :: new_sub_env in
      let free_vars_list = StringSet.elements fvs in
      let num_free_vars = StringSet.cardinal fvs in
      (* Trick, we know the env is a list and lookups will return 1st found, so just add the updated values to the front.
          This new env assumes we have pushed all the closed over values to the stack in order. *)
      let new_sub_env_with_fvs = (List.mapi (fun idx fv -> (fv, RegOffset(~-1 * (1 + idx)*word_size, RBP))) free_vars_list) @ new_sub_env_with_self in
      let new_env = (fname, new_sub_env_with_fvs)::closure_env in
      let (env_with_body_slots, _) = help_aexpr closure_body (num_free_vars + 1) fname new_env in
      (env_with_body_slots, closure_si) in
    match body with
    | ASeq(cexp, aexp, _) ->
        let (lhs_env, lhs_si) = help_cexpr cexp si curr_env_name env in
        help_aexpr aexp lhs_si curr_env_name lhs_env
    | ALet(fname, CLambda(args, body, fvs), let_body, _) ->
        let newenv = add_var_to_env fname (RegOffset(~-si*word_size, RBP)) curr_env_name env in
        let (bindenv, _) = help_closure fname args body fvs 1 newenv in
        help_aexpr let_body (si+1) curr_env_name bindenv
    | ALet(sym, bind, body, _) ->
        let newenv = add_var_to_env sym (RegOffset(~-si*word_size, RBP)) curr_env_name env in
        let (bindenv, newsi) = help_cexpr bind (si+1) curr_env_name newenv in
        help_aexpr body newsi curr_env_name bindenv
    | ALetRec((fname, CLambda(args, body, fvs))::bindings, let_rec_body, let_rec_fvs) ->
        let newenv = add_var_to_env fname (RegOffset(~-si*word_size, RBP)) curr_env_name env in
        let (bindenv, _) = help_closure fname args body fvs 1 newenv in
        (help_aexpr (ALetRec(bindings, let_rec_body, let_rec_fvs)) (si+1) curr_env_name bindenv)
    | ALetRec([], body, _) -> help_aexpr body si curr_env_name env
    | ALetRec _ -> raise (InternalCompilerError "LetRecs cannot have non-CLambda bindings")
    | ACExpr(cexpr) -> help_cexpr cexpr si curr_env_name env
  and help_cexpr (expr : StringSet.t cexpr) (si : int) (curr_env_name : string) (env : arg name_envt name_envt) : arg name_envt name_envt * int =
    match expr with
    | CIf(cond, lhs, rhs, _) ->
        let (lhs_env, lhs_si) = help_aexpr lhs si curr_env_name env in
        help_aexpr rhs lhs_si curr_env_name lhs_env
    | CScIf(cond, lhs, rhs, _) ->
        let (lhs_env, lhs_si) = help_aexpr lhs si curr_env_name env in
        help_aexpr rhs lhs_si curr_env_name lhs_env
    | CPrim1 _ -> (env, si)
    | CPrim2 _ -> (env, si)
    | CApp _ -> (env, si)
    | CImmExpr _ -> (env, si)
    | CTuple _ -> (env, si)
    | CGetItem _ -> (env, si)
    | CSetItem _ -> (env, si)
    | CLambda _ -> raise (InternalCompilerError ("CLambda allocation should be handled by specific help_aexpr ALet/ALetRec cases"))
    | CRecord _ -> (env, si)
    | CGetField _ -> (env, si)
    | CTable _ -> (env, si)
  in
  match fv_prog with
  | AProgram(aexp, fvs) ->
      let (out, _) = help_aexpr aexp 1 "?our_code_starts_here" [("?our_code_starts_here", [])] in
        (prog, out)
