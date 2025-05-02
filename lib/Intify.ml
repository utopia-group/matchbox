open Core

type t =
  | Range of {lo: int; hi: int}
  | Add of t * t
  | Sub of t * t
  | Exp of t * t
  | Times of t * t

let rec to_string = 
  let recurse op e1 e2 = Printf.sprintf "(%s %s %s)" (to_string e1) op (to_string e2) in 
  function 
  | Range {lo;hi} -> 
    if lo = hi then 
      Printf.sprintf "%d" lo
    else 
      Printf.sprintf "[%d,%d]" lo hi
  | Add (e1, e2) -> recurse "+" e1 e2
  | Sub (e1, e2) -> recurse "-" e1 e2
  | Exp (e1, e2) -> recurse "**" e1 e2
  | Times (e1, e2) -> recurse "*" e1 e2

let const i = Range {lo = i; hi = i}

let times e1 e2 = Times (e1, e2)
let shl = times (const 2)
let wc = Range {lo = 0; hi = 1}

let add e1 e2 = Add(e1, e2)

let incr = add (const 1)

let range lo hi = Range {lo; hi}
let range' (lo,hi) = range lo hi

let rec ( ** ) x y = 
  if y < 0 then 
    failwith "integer exponentiation is not closed for negative exponents"
  else if y = 0 then 
    1
  else 
    x * (x ** y)

let rec eval exp : int * int =
  match exp with 
  | Range {lo;hi} -> lo, hi
  | Add (e1, e2) -> 
    let lo1, hi1 = eval e1 in 
    let lo2, hi2 = eval e2 in 
    (lo1 + lo2, hi1 + hi2)
  | Sub (e1, e2) -> 
    let lo1, hi1 = eval e1 in 
    let lo2, hi2 = eval e2 in 
    (lo1 + hi2, hi1 - lo2)
  | Exp (base, power) -> 
    let lobase, hibase = eval base in 
    let lopower, hipower = eval power in 
    (lobase ** lopower, hibase ** hipower)
  | Times (e1, e2) -> 
    let lo1, hi1 = eval e1 in 
    let lo2, hi2 = eval e2 in 
    (lo1 * lo2, hi1 * hi2)

let simplify exp = eval exp |> range'

let of_tv tv = (*tv in big-endian*)
  let rec loop tv = (* tv in little endian*)
    match tv with 
    | [] -> const 0
    | t :: tv' -> 
      let range = 
        let open Trit in 
        match t with 
        | T -> const 1
        | F -> const 0
        | U -> wc
      in 
      loop tv'
      |> shl
      |> add range
    
  in
  List.rev tv
  |> loop


let gen_mask_str x bitwidth i = 
  let bv = Printf.sprintf "%s_%d_bv" x i in
  let mask = Printf.sprintf "%s_%d_mask" x i in
  Printf.sprintf "(= (bvand ((_ int2bv %d) %s) %s) (bvand %s %s))" bitwidth x mask bv mask

let gen_smt_sketch x bitwidth size = 
  List.init size ~f:(gen_mask_str x bitwidth)
  |> String.concat ~sep:" "
  |> Printf.sprintf "(or %s)"
  
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
  let typ = Printf.sprintf "(_ BitVec %d)" w in 
  List.map xs ~f:(fun x -> Printf.sprintf "(declare-const %s %s)" x typ)
  |> String.concat ~sep:"\n"

let gen_tv_sketch x bitwidth lo hi size =
  let vars = gen_vars x size in 
  let vars_str = String.concat vars ~sep:" " in 
  let decls = var_decls vars bitwidth in
  let sketch = gen_smt_sketch x bitwidth size in 
  let max_int_value = Float.(of_int 2 ** of_int bitwidth |> to_int) in 
  Printf.sprintf "%s\n(assert (forall ((%s Int)) \n\t(=> (and (< %s %d) (>= %s 0)) (= (and (<= %s %d) (<= %d %s)) \n\t%s))))\n(check-sat)\n(get-value (%s))\n%!" decls x x max_int_value x x hi lo x sketch vars_str

let parse_model str =
  Printf.printf "Model:\n%s\n%!" str;
  let sexp_model = Parsexp.Many.parse_string_exn str in 
  match sexp_model with 
  | [Atom "sat"; List rst] ->
    List.fold rst ~init:(String.Map.empty) ~f:(fun model sexp -> 
      begin match sexp with 
      | Sexp.List [Atom var; Atom value] -> 
        String.Map.set model ~key:var ~data:(Trit.Vector.of_string value)
      | _ -> 
        failwithf "unrecognized sexp %s" (Sexp.to_string sexp) ()
      end
    ) |> Option.some
  | (Atom "unsat")::_ ->
    None
  | _ -> failwithf "Unrecognized pattern %s" str ()


let get_model sketch = 
  let z3 = Runner.init "/usr/bin/z3 -in" in 
  let response = Runner.run z3 sketch in 
  Printf.printf "%s\n%!" response;
  parse_model response

let get_from_model model x idx suffix = 
  let varname = var_convention x idx suffix in 
  String.Map.find_exn model varname

let extract_tbv_sequence x size model = 
  let lookup = get_from_model model x in
  let f i = 
    let xi = lookup i in 
    Trit.Vector.from_mask_pair (xi `BV) (xi `Mask)
  in
  List.init size ~f

let bitvectors_from_range x bitwidth (lo, hi) = 
  let rec loop size =
    if size > (1 + hi - lo) then 
      failwithf "something went wrong... tried up to size %d, but the naive solution should only take %d (= %d - %d) bitvectors" (size - 1) (hi - lo) hi lo ()
    else
      let sketch = gen_tv_sketch x bitwidth lo hi size in
      match get_model sketch with 
      | None -> loop (size + 1)
      | Some model -> 
        extract_tbv_sequence x size model
  in
  loop 1