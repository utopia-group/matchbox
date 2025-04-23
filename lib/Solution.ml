open Gpl
open Core

type t = {
  name : Var.t;
  params : Var.t list;
  body : Expr.t
}

let to_smtlib {name;params;body} : string = 
  Printf.sprintf "(define-fun %s (%s) (_ BitVec %d)\n\t%s)\n"
    (Var.str name)
    (Var.list_to_smtlib_quant params)
    (Var.width name)
    (Expr.to_smtlib body)


let parse_unop (op : Sexp.t) e =
  match op with 
  | Atom "not" -> Expr.UnOp(Expr.UNot, e)
  | Atom "neg" -> Expr.UnOp(Expr.UNeg, e)
  | Atom s -> failwithf "unrecognized unary operation %s" s ()
  | List _ -> 
    failwithf "Expected a unary operation, got %s" (Sexp.to_string op) () 

let parse_binop (op : Sexp.t) e1 e2 = 
  let open Expr in 
  match op with
  | Atom "bvadd" -> BinOp(BAdd, e1, e2)
  | Atom "bvsub" -> BinOp(BSub, e1, e2)
  | Atom "bvmul" -> BinOp(BMul, e1, e2)
  | Atom "bvor" -> BinOp(BOr, e1, e2)
  | Atom "bvxor" -> BinOp(BXor, e1, e2)
  | Atom "bvand" -> BinOp(BAnd, e1, e2)
  | Atom s -> failwithf "unrecognized binary operation %s" s ()
  | List _ -> failwithf "expected atom binary operation, got %s" (Sexp.to_string op) ()
  
let parse_bitvector a = 
  let a' = String.chop_prefix_exn a ~prefix:"#" in
  match String.get a' 0 with 
  | 'b' -> Expr.bvi (Int.of_string ("0" ^ a')) (String.length a' - 1)
  | 'x' -> Expr.bvi (Int.of_string ("0" ^ a')) (4 * (String.length a' - 1))
  | _ -> failwithf "unrecognized bitstring %s" a ()

let parse_variable params a =
  match List.find params ~f:(fun x -> String.(Var.str x = a)) with
  | None -> failwithf "Could not find %s in %s" a (Var.list_to_smtlib_quant params) ()
  | Some x -> Expr.var x

let rec parse_expr params (sexp : Sexp.t) : Expr.t =
  match sexp with 
  | Atom a -> 
    if String.is_prefix a ~prefix:"#" then 
      parse_bitvector a
    else parse_variable params a
  | List [Atom _; Atom bv; Atom w] -> 
    let width = Int.of_string w in 
    let value_str = String.chop_prefix bv ~prefix:bv |> Option.value_exn ~message:(Printf.sprintf "couldn't parse %s" bv) in
    let value = Int.of_string value_str in 
    Expr.bvi value width
  | List [op; sexp] -> 
    let e = parse_expr params sexp in 
    parse_unop op e
  | List [op; sexp1; sexp2] ->
    let e1 = parse_expr params sexp1 in 
    let e2 = parse_expr params sexp2 in
    parse_binop op e1 e2
  | List (op::_) -> 
    failwithf "unrecognized n-ary (n>2) expression operation %s" (Sexp.to_string op) ()
  | List [] -> 
    failwithf "unrecognized 0-ary expression operation %s" (Sexp.to_string sexp) ()

let parse_bitwidth : Sexp.t -> int = function 
  | List [Atom "_"; Atom "BitVec"; Atom w] -> 
    Int.of_string w
  | s -> failwithf "expected bitvector type, got %s" (Sexp.to_string s) ()

let parse_param : Sexp.t -> Var.t = function
  | List [Atom x; bitwidth] -> 
    parse_bitwidth bitwidth
    |> Var.make x
  | x -> 
    failwithf "unrecognized param %s" (Sexp.to_string x) ()

let parse_params = List.map ~f:parse_param 
let extract (body : string) : t list = 
  match Parsexp.Single.parse_string_exn body with 
  | Atom a -> 
    failwithf "Did not recognize bare atom %s" a ()
  | List funs -> 
    List.map funs ~f:(fun sexp -> 
      match sexp with 
      | List [Atom "define-fun"; Atom name; List params;
              bitwidth; expr] -> 
        let params = parse_params params in 
        {
          name = Var.make name (parse_bitwidth bitwidth); 
          params = params;
          body = parse_expr params expr
          }
      | _ -> 
        failwithf "unrecognized function %s" (Sexp.to_string sexp) ()
    )

let fun_to_outvar f = Var.make (Var.str f |> String.lowercase) (Var.width f)

let dead_code_elim invocations solution = 
  let vars = Expr.vars solution.body in 
  let not_dead (f, args) = List.exists args ~f:(Var.Set.mem vars) || Var.Set.mem vars (fun_to_outvar f) in 
  List.filter invocations ~f:not_dead



let args_to_string xs = 
  List.map ~f:Var.str xs
  |> String.concat ~sep:","

let pretty_print (observations : Var.t list) (invocations : (Var.t * Var.t list) list) (solution : t) : string =
  let obs_params, func_params = List.split_n solution.params (List.length observations) in 
  let solution = { solution with 
    params = func_params;
    body = List.fold2_exn obs_params observations ~init:solution.body ~f:(fun body param arg -> 
      Expr.subst param (Expr.var arg) body
    )
  } in 
  let invocations = dead_code_elim invocations solution in 
  let head = Printf.sprintf "%s = %s(%s)" (Expr.to_smtlib solution.body) (Var.str solution.name) (args_to_string solution.params) in
  let body = List.map invocations ~f:(fun (f, xs) -> Printf.sprintf "\n     %s = %s(%s)" (Var.str (fun_to_outvar f)) (Var.str f) (args_to_string xs)) |> String.concat ~sep:",\n     " in
  Printf.sprintf {|
%s :- %s.
  |} head body