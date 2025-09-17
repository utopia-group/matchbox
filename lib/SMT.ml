open Core

type tactical = Sexp.t
let t_to_string = Sexp.to_string

type sort = Sexp.t
let s_to_string = Sexp.to_string

type expr = Sexp.t
let e_to_string = Sexp.to_string

type command = Sexp.t
let c_to_string = Sexp.to_string

type program = command list
let p_to_string sexps = 
  List.map sexps ~f:Sexp.to_string
  |> String.concat ~sep:"\n"

let bv_sort w = Sexp.(List [
    Atom "_";
    Atom "BitVec";
    Atom (Int.to_string w)
  ])

let bv value width = 
  Sexp.(List [
    Atom "_";
    Atom (Printf.sprintf "bv%d" value);
    Atom (Int.to_string width)
  ])

let bv' bits = 
  Sexp.Atom ("#b" ^ Bit.Vector.to_string bits)

let var x = Sexp.Atom x
let int i = Sexp.Atom (Printf.sprintf "%d" i)
let real i = Sexp.Atom (Printf.sprintf "%f" i)

let int_sort = Sexp.Atom "Int"
let real_sort = Sexp.Atom "Real"
let check_sat = Sexp.(List [Atom "check-sat"])

let check_sat_using tactical = 
  Sexp.(List [Atom "check-sat-using"; tactical])

let get_model = Sexp.(List [Atom "get-model";])
let exit = Sexp.(List [Atom "exit"])
let declare_const x sort = 
  Sexp.(List [
    Atom "declare-const";
    Atom x;
    sort
  ])

let declare_fun f arg_sorts return_sort =
  let open Sexp in 
  List [
    Atom "declare-fun";
    Atom f;
    List arg_sorts;
    return_sort
  ]

let tactical name tacticals = Sexp.(List (Atom name :: tacticals))
let then_ = tactical "then"
let par_then = tactical "par-then"
let par_or = tactical "par-or"
let or_else = tactical "or-else"
let repeat t = tactical "repeat" [t]
let repeat' t n = tactical "repeat" [t; int n]
let try_for t ms = tactical "repeat" [t; real ms]
let using_params (t : tactical) params =
  tactical "using-params" @@ 
  t :: (
    List.bind params ~f:(fun (param, arg) -> 
      [Sexp.Atom (":" ^ param);
      arg]
    )
  )

let tactic tact : tactical = Sexp.Atom tact

let rec subst (sexp : expr) (x : string) (e : expr) : expr = 
  match sexp with 
  | Atom a when String.(a = x) -> e
  | Atom _ -> sexp
  | List es -> List (List.map es ~f:(fun sexp -> subst sexp x e))

let get_value variables = 
  let xs = List.map variables ~f:(fun x -> Sexp.Atom x) in 
  Sexp.(List [Atom "get-value"; List xs])

let assert_ (sexp : expr) : command = Sexp.List [(Atom "assert"); sexp]
let minimize (sexp : expr) : command = Sexp.List [(Atom "minimize"); sexp]
let maximize (sexp : expr) : command = Sexp.List [(Atom "maximize"); sexp]

let apply_sexp a es = Sexp.List (a :: es)
let apply f = apply_sexp (Sexp.Atom f)

let symb = apply

(* logic *)
let true_ = Sexp.Atom "true"
let false_ = Sexp.Atom "false"
let and_ phis = if List.is_empty phis then true_ else apply "and" phis
let iff = apply "="
let or_ = apply "or"
let implies = apply "=>"
let not phi = apply "not" [phi]

let ite cond e1 e2 = apply "ite" [cond; e1; e2]

(* quantifiers *)
let quantifier q (sorted_vars : (string * sort) list) (phi : expr) =
  Sexp.(
    let variables = 
      List.map sorted_vars ~f:(fun (x, s) -> 
        List [Atom x; s]
      )
    in
    List [
      Atom q; 
      List variables;
      phi
    ]
  )

let forall = quantifier "forall"
let exists = quantifier "exists"


(* arithmetic operators *)
let (+) = apply "+"
let (-) = apply "-"
let ( * ) = apply "*"
let div = apply "div"
let ( mod ) = apply "mod"
let ( = ) = apply "="
let ( < ) = apply "<"
let ( > ) =  apply ">"
let (<=) = apply "<="
let (>=) = apply ">="
let distinct = apply "distinct"

let modeq e1 e2 m =
  (=) [(mod) [e1; m]; (mod) [e2; m]]

(* conversion from int to bitvector *)
let int2bv w (x : expr) : expr = 
  Sexp.List [
    (apply "_" [Atom "int2bv"; int w]);
    x
  ]


(* bitvector arithmetic *)
let bvadd = apply "bvadd"
let bvmul = apply "bvmul"
let bvsub = apply "bvsub"

(* bitvector resizing *)
let concat = apply "concat"
let extract ~hi ~lo = 
  apply_sexp Sexp.(List [
    Atom "_"; 
    Atom "extract";
    Atom (Int.to_string hi);
    Atom (Int.to_string lo)])

(* bitwise operations *)
let bvand = apply "bvand"
let bvor = apply "bvor"


(* unsigned comparison *)
let bvult = apply "bvult"
let bvule = apply "bvule"
let bvugt = apply "bvugt"
let bvuge = apply "bvuge"
(* signed comparison *)
let bvsle = apply "bvsle"
let bvslt = apply "bvslt"
let bvsgt = apply "bvsgt"
let bvsge = apply "bvsge"
let bvlshr = apply "bvlshr"


let rec of_expr expr : expr =
  let module E = Gpl.Expr in
  match expr with 
  | E.BV (v,w) -> 
    bv (Bigint.to_int_exn v) w
  | E.Var x -> var (Gpl.Var.str x)
  | E.BinOp(op, e1, e2) -> 
    let args = [of_expr e1; of_expr e2] in
    begin match op with 
    | E.BAdd -> bvadd args
    | E.BSub -> bvsub args
    | E.BMul -> bvmul args
    | E.BAnd -> bvand args
    | E.BOr -> bvor args
    | E.BXor -> failwith "implement xor"
    | E.BAshr -> failwith "implement >>a"
    | E.BLshr -> bvlshr args
    | E.BShl -> failwith "implement <<"
    end
  | E.UnOp (op, e) ->
    let arg = of_expr e in
    begin match op with 
    | E.UNot -> not arg
    | E.UNeg -> failwith "implement bvneg"
    end
  | E.Apply(f, _, args) ->
    List.map args ~f:of_expr
    |> apply (Gpl.Var.str f)

let rec of_bexpr bexpr : expr = 
  let module B = Gpl.BExpr in
  match bexpr with
  | B.TTrue -> true_
  | B.TFalse -> false_
  | B.TNary(bop, bs) -> 
    let args = List.map bs ~f:of_bexpr in
    begin match bop with 
    | B.LAnd -> and_ args
    | B.LOr -> or_ args
    | B.LArr -> implies args
    | B.LIff -> iff args
    end
  | B.TComp(cmp, e1, e2) -> 
    let args = [of_expr e1; of_expr e2] in
    begin match cmp with 
    | B.Eq -> (=) args
    | B.Sge -> bvsge args
    | B.Sgt -> bvsgt args
    | B.Slt -> bvslt args
    | B.Sle -> bvsle args
    | B.Uge -> bvuge args
    | B.Ugt -> bvugt args
    | B.Ult -> bvult args
    | B.Ule -> bvule args
    end
  | B.Exists (x, b) -> 
    of_bexpr b
    |> exists [Gpl.Var.str x, bv_sort (Gpl.Var.width x)]
  | B.Forall (x, b) -> 
    of_bexpr b
    |> forall [Gpl.Var.str x, bv_sort (Gpl.Var.width x)]
  | B.TNot b -> 
    of_bexpr b
    |> not

type response = Sexp.t list

let run (r : Runner.t) (p : program) : response =
  Runner.run r (p_to_string p)
  |> Parsexp.Many.parse_string_exn


module Model = struct
  type 'a t = 'a String.Map.t

  let empty : 'a t = String.Map.empty

  let extract sexp_model = 
    match sexp_model with 
    | Sexp.List rst ->
      List.fold rst ~init:(String.Map.empty) ~f:(fun model sexp -> 
        begin match sexp with 
        | Sexp.List [Atom var; Atom value] -> 
          Map.set model ~key:var ~data:value
        | _ -> 
          failwithf "unrecognized sexp %s" (Sexp.to_string sexp) ()
        end
      )
    | _ -> failwithf "Unrecognized pattern %s" (Sexp.to_string sexp_model) ()


  let parse str =    
    Printf.printf "Model:\n%s\n%!" str;
    Parsexp.Single.parse_string_exn str
    |> extract

  let map (model : 'a t) ~f : 'b t = 
    String.Map.map model ~f

  let find_exn (model : 'a t) (key : string) = 
    Map.find model key
    |> Option.value_exn ~message:("couldn't find " ^ key ^ " in SMT model")

  let find (model : 'a t) (key : string) = 
    Map.find model key
end

let check (resp : response) : string Model.t option =
  Printf.printf "%s\n%!" (List.map resp ~f:(Sexp.to_string) |> String.concat ~sep:"\n");
  match resp with 
  | [] -> failwith "Received empty response from solver"
  | (Atom "sat") :: rst -> 
    begin match List.hd rst with 
    | Some model_sexp -> Some (Model.extract model_sexp)
    | None -> Some (Model.empty) 
    end
  | (Atom "unsat"):: _ -> None
  | _ -> failwithf "Did not recognize response from solver %s" (Sexp.to_string (Sexp.List resp)) ()

