open Core
open Gpl


type tactic = SMT

type command = 
  | CheckSat of tactic option
  | GetModel

let c_to_string = function 
  | CheckSat None -> "(check-sat)"
  | CheckSat (Some SMT) -> "(check-sat-using :smt)"
  | GetModel -> "(get-model)"

type t = {
  consts : Var.t list;
  funcs : (Var.t * (int list)) list; 
  assts : (BExpr.t) list;
  cmnds : command list;
}

let concatmap ~f ~sep xs =
  List.map xs ~f |> String.concat ~sep

let to_string ({consts; funcs; assts; cmnds} : t) = 
  let consts_str = consts |> concatmap ~f:Var.to_smtlib_decl ~sep:"\n" in
  let funcs_str = funcs |> concatmap ~sep:"\n" ~f:(fun (f,ins) ->
    let ins_str = ins |> concatmap ~f:(Printf.sprintf "(_ BitVec %d)") ~sep:" " in
    Printf.sprintf "(declare-fun %s (%s) (_ BitVec %d))" (Var.str f) ins_str (Var.width f)
  ) in
  let assts_str = assts |> concatmap ~sep:"\n" ~f:(fun phi -> Printf.sprintf "(assert %s)" (BExpr.to_smtlib phi))in
  let cmnds_str = cmnds |> concatmap ~f:c_to_string ~sep:"\n" in
  [ consts_str
  ; funcs_str
  ; assts_str
  ; cmnds_str ] |> String.concat ~sep:"\n"
  

let smt_gen (phi : BExpr.t) : t = 
  let consts = BExpr.free_vars phi |> Set.to_list in 
  let funcs = BExpr.get_funs phi |> List.dedup_and_sort ~compare:(fun (x,_) (y, _) -> Var.compare x y) in 
  let assts = [phi] in 
  let cmnds = [CheckSat None] in 
  {
    consts; funcs; assts; cmnds
  }

(** lowercased [str] [contains] lowercased [substring] *)
let contains str substring = 
  String.lowercase str
  |> String.is_substring ~substring:(String.lowercase substring)


let is_unknown (result : string) : bool = 
  contains result "unknown"

let is_unsat (result : string) : bool = 
  Printf.printf "%s\n%!" result;  
  contains result "unsat" && not (is_unknown result)
    
let is_sat (result : string) : bool = 
  contains result "sat" 
  && not (is_unsat result) 
  && not (is_unknown result)


let check phi =
  phi
  |> smt_gen
  |> to_string
  |> Runner.(run (init "z3 -smt2 -in"))


let satisfiable (phi : BExpr.t) : bool = 
  check phi 
  |> is_sat


let verify (phi : BExpr.t) : bool = 
  BExpr.not_ phi
  |> check
  |> is_unsat
