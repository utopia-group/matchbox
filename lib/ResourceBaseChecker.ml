open Core
open BaseLogic

type rsc = int
type ctx = rsc String.Map.t

let (@) (c1 : ctx) (c2 : ctx) : ctx = 
  Map.merge c1 c2 ~f:(fun ~key:_ -> function 
    | `Left n | `Right n -> Some n
    | `Both (n,m) -> Some (Int.min n m)
  )


let find_cost ctx symbol = Map.find_exn ctx (Symbol.to_string symbol)

let rec calculate_max_cost (ctx : ctx) : Clause.t -> rsc = function
  | Id (f, _) -> find_cost ctx f
  | Compose (f, _, _) | MapOut (f, _, _) | MapIn(f, _, _) -> 
    calculate_max_cost ctx f
  | Table (t, _) ->
    List.length t
  | Join (f, g, _) -> 
    calculate_max_cost ctx f * calculate_max_cost ctx g
  | Override (_f, _g, _) ->
    failwith "TODO"
