open Assembly
open Errors
open Exprs
open Graph
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

let interfere (e : StringSet.t aexpr) (live : StringSet.t) : grapht =
  raise (NotYetImplemented "Generate interference graphs from expressions for racer")
;;

let color_graph (g: grapht) (init_env: arg name_envt) : arg name_envt =
  raise (NotYetImplemented "Implement graph coloring for racer")
;;

let register_allocation (prog: tag aprogram) : tag aprogram * arg name_envt name_envt =
  raise (NotYetImplemented "Implement register allocation for racer")
;;