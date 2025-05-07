open Core

module Exp = struct 
  type op = 
  | Mod
  | Add
  | Sub
  | Mul
  | Div

  let op_to_string op : string -> string -> string = 
    let infix op arg1 arg2 = Printf.sprintf "(%s%s%s)" arg1 op arg2 in 
    match op with 
    | Mod -> 
      infix " mod "
    | Add -> 
      infix " + "
    | Sub -> 
      infix " - "
    | Mul -> 
      infix "*"
    | Div -> 
      infix "/"

  let op_to_smt = function 
    | Mod -> SMT.(mod)
    | Add -> SMT.(+)
    | Sub -> SMT.(-)
    | Mul -> SMT.( * )
    | Div -> SMT.div

  type t =
  | Int of int
  | Var of string
  | AOp of op * t * t

  let rec to_string = function 
    | Int i -> Int.to_string i
    | Var x -> x
    | AOp (a, e1, e2) -> 
      op_to_string a (to_string e1) (to_string e2)

  let rec to_smt = function 
    | Int i -> SMT.int i
    | Var x -> SMT.var x
    | AOp (op, e1, e2) -> 
      op_to_smt op [to_smt e1; to_smt e2]

  let const i = Int i 
  let var x = Var x

  let mkop op e1 e2 = AOp (op, e1, e2) 

  let times = mkop Mul
  let add = mkop Add
  let div = mkop Div
  let rec cexp e i = 
    if i < 0 then 
      failwith "negative exponentiation is not closed in the integers"
    else if i = 0 then 
      const 1
    else if i = 1 then 
      e
    else
      times e (cexp e (i-1))

  let modi e i = mkop Mod e (const i)

  let xdiv x = div (var x)
      
  let incr = add (const 1)
  let rec exp2' i =
    if i < 0 then 
      failwith "[exp2] cannot take a negative exponent of 2"      
  else if i = 0 then 
    1
  else 2 * exp2' (i - 1)

  let exp2 i : t = const (exp2' i)

end 

module Form = struct 
  type lop =
    | And | Or | Iff | Imp

  type cmp = 
    | Gt | Lt | Ge | Le | Eq

  type t = 
    | True
    | False 
    | Not of t
    | LOp of lop * t * t
    | Cmp of cmp * Exp.t * Exp.t


  let mkcmp c e1 e2 = Cmp (c, e1, e2)
  
  let eq e1 e2 = mkcmp Eq e1 e2

  let xeq x e = eq Exp.(var x) e

  let mkop o e1 e2 = LOp (o, e1, e2)

  let and_ = mkop And
  
  let of_tv x tv : t = (*tv in big-endian*)
    let rec loop i tv = (* tv in little endian*)
      let open Trit in  
      match tv with 
      | [] -> xeq x Exp.(const 0)
      | U :: tv' -> loop (i+1) tv'
      | b :: tv' -> 
        let ith_bit = Exp.(modi (xdiv x (exp2 i)) 2) in
        let b_int = if get_bit_exn b then Exp.const 1 else Exp.const 0 in
        and_ (eq ith_bit b_int) (loop (i+1) tv')
    in
    List.rev tv
    |> loop 0 

end

let e_sp x e bitwidth =
  let x' = x ^ "$1" in 
  let modulus = Exp.(to_smt (exp2 bitwidth)) in 
  (x' , SMT.(modeq (var x') e modulus))


let gen_mask x_str bitwidth i = 
  let open SMT in 
  let x = var x_str in 
  let bv = var (Printf.sprintf "%s_%d_bv" x_str i) in
  let mask = var (Printf.sprintf "%s_%d_mask" x_str i) in
  (=) [
    bvand [(int2bv bitwidth x); mask]; 
    bvand [bv; mask]
  ]

  let gen_smt_sketch x bitwidth size = 
  SMT.or_ (List.init size ~f:(gen_mask x bitwidth))
    
let var_convention x idx suffix =
  let root = Printf.sprintf "%s_%d" x idx in 
  match suffix with 
  | `Var -> root
  | `BV -> root ^ "_bv" 
  | `Mask -> root ^ "_mask"

let gen_vars x size =
  List.init size ~f:(fun i -> 
    [var_convention x i `BV;
     var_convention x i `Mask]
  ) |> List.concat

let var_decls xs w = 
  let decl x = SMT.(declare_const x (bv_sort w)) in 
  List.map xs ~f:decl

let matches_tv x_str tv = 
  let open SMT in 
  let bitwidth = List.length tv in 
  let (v, m) = Trit.Vector.to_bitmask tv in 
  let value = bv' v in 
  let mask = bv' m in 
  (=) [
    bvand [int2bv bitwidth (var x_str); mask];
    bvand [value; mask]
  ]


let gen_tv_sketch x tv e size : string * SMT.program =
  let bitwidth = Trit.Vector.length tv in 
  let precond = matches_tv x tv in
  let (x', postcond) = e_sp x (Exp.to_smt e) bitwidth in 
  let sketch = gen_smt_sketch x' bitwidth size in 
  let vars = gen_vars x' size in 
  x',
  SMT.(List.concat [
    var_decls vars bitwidth;
    [assert_ (forall [x, int_sort; x', int_sort] @@ 
      implies [
        postcond;
        iff [precond; sketch]
      ])
    ];
    [check_sat];
    [get_value vars]
  ])


let get_from_model model x idx suffix = 
  let varname = var_convention x idx suffix in 
  SMT.Model.find_exn model varname
  |> Trit.Vector.of_string

let extract_tbv_sequence x size model = 
  let lookup = get_from_model model x in
  let f i = 
    let xi = lookup i in 
    Trit.Vector.from_mask_pair (xi `BV) (xi `Mask)
  in
  List.init size ~f

let realize_operation x tv op  = 
  let rec loop size =
    let x', sketch = gen_tv_sketch x tv op size in
    let result = SMT.run (Runner.init "z3 -smt2 -in") sketch in
    match SMT.check result with
    | None -> loop (size + 1)
    | Some model ->
      extract_tbv_sequence x' size model
  in
  loop 1