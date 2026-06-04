open Core
open Primitives
include Cmd.Make (Active)

let assign x e = prim (Active.assign x e)

let ite b c1 c2 =
  choice
    (seq (assume b) c1)
    (seq (assume (BExpr.not_ b)) c2)

let rec wp phi cmd =
  match cmd with
  | Seq cs ->
    List.fold_right cs
      ~init:phi
      ~f:(fun c phi -> wp phi c)
  | Choice cs ->
    List.map cs ~f:(wp phi)
    |> BExpr.ands
  | Prim p ->
    match p with
    | Passive (Assume psi) ->
      BExpr.imp [psi; phi]
    | Passive (Assert psi) ->
      BExpr.and_ psi phi
    | Assign (x,e) ->
      BExpr.subst x e phi