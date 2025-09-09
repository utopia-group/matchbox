open Core
open BaseLogic

type rsc = int
type ctx = rsc String.Map.t


let find_cost ctx symbol = Map.find_exn ctx (Symbol.to_string symbol)

let rec calculate_max_cost (ctx : ctx) : Clause.t -> rsc = function
  | Id f -> find_cost ctx f
  | Compose (f, _) | MapOut (f, _) | MapIn(f, _) -> 
    calculate_max_cost ctx f
  | Join (f, g, _) -> 
    calculate_max_cost ctx f * calculate_max_cost ctx g