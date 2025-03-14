open Gpl
open Stijl

let v32 str = Var.make str 32
let v9 str = Var.make str 9
let v48 str = Var.make str 48

let metadata = v9 "metadata1"
let eth_dst = v48 "eth.dst"
let eth_src = v48 "eth.src"
let eth_dst' = v48 "eth.dst1"
let eth_src' = v48 "eth.src1"
let ipv4_dst = v32 "ipv4.dst"
let ipv4_dst' = v32 "ipv4.dst1"
let port = v9 "port" 
let port' = v9 "port1"

let drop p = Primitives.Action.([], [
    assign p @@ Expr.bvi 511 9
  ])

let route = Primitives.Action.( [v48 "dmac"; v9 "p"], [
  assign port @@ Expr.var @@ v9 "p";
  assign eth_src @@ Expr.var eth_dst;
  assign eth_dst @@ Expr.var @@ v48 "dmac"])
let ipv4_route = GPL.table "ipv4_route" [(ipv4_dst, Exact)] [route; drop port]

let fwd = Primitives.Action.([v9 "p1"], [
   assign port' @@ Expr.var @@ v9 "p1"
])
let ipv4_fwd = GPL.table "ipv4_fwd" [(ipv4_dst', Exact)] [fwd; drop port']

let rewrite = [v48 "dmac1"], Primitives.Action.[
  assign eth_src' @@ Expr.var eth_dst';
  assign eth_dst' @@ Expr.var @@ v48 "dmac1";
]
let ipv4_rewrite = GPL.(
  table "ipv4_rewrite" [(ipv4_dst', Exact)] [
    rewrite; ([],[])
  ])

let seq (params1, acts1)  (params2, acts2) =
  (params1 @ params2, acts1 @ acts2)

let set_metadata = Primitives.Action.([v9 "m1"], [
  assign metadata @@ Expr.var @@ v9 "m1"
])

let lag = 
  GPL.table "aggregate" [(ipv4_dst', Exact)] [
    set_metadata 
  ]

let next = 
  GPL.table "next" [(metadata, Exact)] [
    seq fwd rewrite;
    drop port'
  ]


let () = 
  let p = ipv4_route in
  let (_ : GPL.t) = GPL.(sequence [ipv4_fwd; ipv4_rewrite]) in
  let q = GPL.(sequence [lag; next]) in
  let pre, post = 
    let open BExpr in 
    let open Expr in 
    (ands [
      var ipv4_dst == var ipv4_dst';
      var eth_dst == var eth_dst';
      var eth_src == var eth_src';
    ], ands [
      var ipv4_dst == var ipv4_dst';
      var eth_dst == var eth_dst';
      var eth_src == var eth_src';
      var port == var port';
    ])
  in
  SygusGen.gen_assumption p q pre post
  |> SyGuS.to_string
  |> Printf.printf "%s\n%!"