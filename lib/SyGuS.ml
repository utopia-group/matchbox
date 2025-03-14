open Core
open Gpl

let concat_map ~f ~sep xs = 
  List.map ~f xs |> String.concat ~sep

module Production = struct
  type t = {
    symbol : Var.t;
    options : Expr.t list;
  }
  let to_string production = 
    Printf.sprintf "  (%s (_ BitVec %d) ((Constant (_ BitVec %d)) %s))"
      (Var.str production.symbol)
      (Var.width production.symbol)
      (Var.width production.symbol)
      (concat_map ~f:(Expr.to_smtlib) ~sep:" " production.options)

end

module Grammar = struct
  type t = {
    nonterminals : Var.t list; 
    productions : Production.t list; 
  }
  let to_string ({nonterminals; productions} : t) =
    let nonterms = Var.list_to_smtlib_quant nonterminals in
    let prods = concat_map ~sep:"\n" ~f:Production.to_string productions  in
    Printf.sprintf "(%s)\n(%s)" nonterms prods
end

module SynthFun = struct
  type t  = {
    symbol : Var.t;
    variables : Var.t List.t;
    grammar : Grammar.t; 
  }
  let to_string {symbol; variables; grammar} = 
    Printf.sprintf "(synth-fun %s (%s) (_ BitVec %d)\n  %s)"
      (Var.str symbol)
      (Var.list_to_smtlib_quant variables)
      (Var.width symbol)
      (Grammar.to_string grammar)

end

type t = { 
  funs : SynthFun.t List.t;
  variables : Var.t List.t;
  constraints  : BExpr.t List.t;
}

let var_decl x = 
  Printf.sprintf "(declare-var %s (_ BitVec %d))" (Var.str x) (Var.width x)

let constraint_to_sygus phi =
  BExpr.to_smtlib phi
  |> Printf.sprintf "(constraint %s)"

let to_string ({funs; variables; constraints} : t) =
  let fs = funs |> concat_map ~sep:"\n" ~f:(SynthFun.to_string) in
  let vars = variables |> concat_map ~sep:"\n" ~f:(var_decl) in
  let cnstrs = constraints |> concat_map ~sep:"\n" ~f:(constraint_to_sygus) in
  Printf.sprintf {|
;; Functions to Synthesize
%s
;; Variables
%s
;; Constraints
%s
(check-synth)
|} fs vars cnstrs
