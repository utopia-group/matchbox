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
let and_ = apply "and"
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
          String.Map.set model ~key:var ~data:value
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
    String.Map.find model key
    |> Option.value_exn ~message:("couldn't find " ^ key ^ " in SMT model")

  let find (model : 'a t) (key : string) = 
    String.Map.find model key
end

let check (resp : response) : string Model.t option =
  match resp with 
  | [] -> failwith "Received empty response from solver"
  | (Atom "sat") :: rst -> 
    begin match List.hd rst with 
    | Some model_sexp -> Some (Model.extract model_sexp)
    | None -> Some (Model.empty) 
    end
  | (Atom "unsat"):: _ -> None
  | _ -> failwithf "Did not recognize response from solver %s" (Sexp.to_string (Sexp.List resp)) ()

