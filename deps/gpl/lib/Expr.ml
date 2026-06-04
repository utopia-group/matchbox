open Core
type bop =
  | BAnd
  | BOr
  | BAdd
  | BMul
  | BSub
  | BXor
  | BShl
  | BAshr
  | BLshr
  [@@deriving eq, sexp, hash, compare, quickcheck]

let bop_to_smtlib = function
  | BAnd -> "bvand"
  | BOr -> "bvor"
  | BXor -> "bvxor"
  | BAdd -> "bvadd"
  | BMul -> "bvmul"
  | BSub -> "bvsub"
  | BShl -> "bvshl"
  | BAshr -> "bvashr"
  | BLshr -> "bvlshr"

type uop =
  | UNot
  | UNeg
  [@@deriving eq, sexp, hash, compare, quickcheck]

            
let uop_to_smtlib = function
  | UNot ->
    "bvnot"
  | UNeg -> 
    "bvneg"

type t =
  | BV of Bigint.t * int
  | Var of Var.t
  | BinOp of bop * t * t
  | UnOp of uop * t
  | Apply of Var.t * int list * t list
  [@@deriving eq, sexp, hash, compare]

let rec to_smtlib = function
  | BV (n,w) ->
    Printf.sprintf "(_ bv%s %d)" (Bigint.to_string n) w
  | Var x -> Var.str x
  | BinOp (op, e1, e2) ->
    Printf.sprintf "(%s %s %s)"
      (bop_to_smtlib op)
      (to_smtlib e1)
      (to_smtlib e2)
  | UnOp (op,e) ->
    Printf.sprintf "(%s %s)" (uop_to_smtlib op) (to_smtlib e)
  | Apply (f, _, es) -> 
    Printf.sprintf "(%s %s)" (Var.str f) 
      (List.map ~f:to_smtlib es |> String.concat ~sep:" ")


let rec width = 
  function 
  | BV (_,w) -> w
  | Var x -> Var.width x
  | UnOp(_, e) -> width e
  | BinOp(_, e1, e2) -> 
    assert (width e1 = width e2);
    width e1
  | Apply(f, _, _) -> Var.width f

let bv n w = BV (Bigint.(n % pow (succ one) (of_int w)), w)
let bvi n w = bv (Bigint.of_int n) w
let var x = Var x

let ( $* ) f es = Apply(f, List.map ~f:width es, es)
let ( $ ) f e = f $* [e]  

let eval2 op e1 e2 =
  match e1, e2 with
  | BV(v1, w1), BV (v2, w2) ->
    assert (w1 = w2);
    begin match op with
      | BAnd ->
        bv Bigint.(v1 land v2) w1
      | BOr ->
        bv Bigint.(v1 lor v2) w1
      | BAdd ->
        bv Bigint.(v1 + v2) w1
      | BMul ->
        bv Bigint.(v1 * v2) w1
      | BSub ->
        bv Bigint.(v1 - v2) w1
      | BXor ->
        bv Bigint.(v1 lxor v2) w1
      | BShl ->
        bv Bigint.(shift_left v1 (to_int_exn v2)) w1
      | BAshr ->
        bv Bigint.(v1 asr (to_int_exn v2)) w1
      | BLshr ->
        (* WARNING -- is this the right shift?*)
        bv Bigint.(shift_right v1 (to_int_exn v2)) w1
    end
  | _ -> BinOp(op, e1, e2)

let eval1 op e1 =
  match e1 with
  | BV(v1, w1) ->
      begin match op with
      | UNot ->
        bv Bigint.(lnot v1) w1
      | UNeg -> 
        bv (Bigint.(zero - (v1 % ((of_int 2 ** of_int w1) - one)))) w1
      end
  | _ -> UnOp(op, e1)

let get_value = function
  | BV (v, w) -> Result.return (v,w)
  | e ->
    Printf.sprintf "Couldnt get value from non-BV expression: %s" (to_smtlib e)
    |> Result.fail

let eval (model : Model.t) expr : ((Bigint.t * int), string) Result.t =
  let open Result.Let_syntax in
  let rec loop e =
    match e with
    | Apply _ -> failwith "unimplemented"
    | BV (v,w) -> return (v,w)
    | Var x ->
      begin match Model.lookup model x with
        | None ->
          Printf.sprintf "Model is missing %s:\n%s"
            (Var.str x) (Model.to_string model)
          |> Result.fail
        | Some v ->
          return v
      end
    | UnOp (op, e) ->
      let%bind v,w = loop e in
      eval1 op (bv v w)
      |> get_value
    | BinOp (op, e1, e2) ->
      let%bind v1,w1 = loop e1 in
      let%bind v2,w2 = loop e2 in
      eval2 op (bv v1 w1) (bv v2 w2)
      |> get_value
  in
  loop expr

let subst x e =
  let rec subst' = function
    | BV (v, w) -> BV (v,w)
    | Var y when Var.equal x y -> e
    | Var y -> Var y
    | UnOp(op, e) -> UnOp(op, subst' e)
    | BinOp (op, e1, e2) -> BinOp (op, subst' e1, subst' e2)
    | Apply (f, ws, es) -> Apply (f, ws, List.map es ~f:subst')
  in
  subst'

let rec vars = 
  let open Var.Set in 
  function
  | BV _ -> empty
  | Var x -> singleton x 
  | UnOp(_, e) -> vars e
  | BinOp(_, e1, e2) -> Set.union (vars e1) (vars e2)
  | Apply (_,_, es) -> union_list @@ List.map ~f:vars es


let rec get_funs e = 
  match e with 
  | BV _ | Var _ -> []
  | BinOp (_, e1, e2) -> get_funs e1 @ get_funs e2
  | UnOp (_, e) -> get_funs e
  | Apply (f, ws, _) -> [(f, ws)] 

let rec size e = 
  match e with 
  | BV _ | Var _ -> 1
  | BinOp (_, e1, e2) -> size e1 + 1 + size e2
  | UnOp (_, e) -> 1 + size e 
  | Apply (_,_, es) -> 1 + List.sum (module Int) es ~f:size