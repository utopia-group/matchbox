open Core

module MakeExpr ( T : sig 
    type t
    val (=) : t -> t -> bool 
end) = struct

  type t = 
    | V of string * T.t
    | F of string * T.t * T.t
    | A of t * t

  let rec to_string = function
  | V (s,_) -> s
  | F (f,_,_) -> f
  | A (f, e) -> Printf.sprintf "%s(%s)" (to_string f) (to_string e)


  let hastype typ' (_, typ) = T.(typ = typ')

  let rec tygus vars funs typ =
    match List.find vars ~f:(hastype typ) with
    | Some (x,t) -> Some (V (x,t))
    | None -> 
      List.find_map funs ~f:(fun (f, i, o) -> 
        if T.(o = typ) then 
          begin match tygus vars funs i with
            | None -> None
            | Some e -> Some (A (F (f,i,o), e))
          end
        else
          None
      )

  let rec tygus_stream vars funs typ : t Stream.t = 
    let open Stream in 
    let vs = Stream.of_list vars in 
    let fs = Stream.of_list funs in 
    filter_map vs ~f:(fun (x,t) -> 
      if T.(t = typ) then 
        Some (V (x,t))
      else 
        None)
    ++ lazy (bind fs ~f:(fun (f, i, o)  ->
      let funs = List.filter funs ~f:(fun (g,_,_) -> String.(g <> f)) in 
      if T.(typ = o) then
        filter_map (tygus_stream vars funs i) ~f:(fun e -> 
          Some (A (F (f,i,o), e)))
      else
        Nil
    ))
end

module BVExpr = struct 
  open Gpl
  include MakeExpr (Int)
  let rec to_expr = function
  | V (x, w) -> Expr.var (Var.make x w)
  | A(F (f, _, o), e) -> Expr.(Var.make f o $ to_expr e)
  | _ -> failwith "could not convert to expr"
end
let comp () = BVExpr.tygus_stream [
  "ipv4.dst", 32;
] [
  "LAG", 32, 32;
  "NEXT", 32, 9;
] 9

module MakeForm (TyGuS : sig
  type t
  val tygus_stream : (string * int) list -> (string * int * int) list -> int -> t Stream.t
  val to_expr : t -> Gpl.Expr.t
end ) = struct 
  open Gpl

  type asgn = { 
    func : string * int;
    arg : string * int;
    body : Expr.t }

  type t =
    | Asgn of asgn
    | Cond of BExpr.t * t
    | And of t list

  let to_string =
    let rec indent depth = 
      if depth = 0 then "" else "  " ^ indent (depth - 1)
    in
    let rec loop depth = function 
    | Asgn {func; arg; body} -> 
      Printf.sprintf "%s%s(%s) :- %s" (indent depth) (fst func) (fst arg) (Expr.to_smtlib body)
    | Cond (phi, rst) ->
      Printf.sprintf "%s%s -->\n%s" (indent depth) (BExpr.to_smtlib phi) (loop (depth + 1) rst)
    | And ts -> 
      List.map ts ~f:(loop depth)
      |> String.concat ~sep:"\n"
    in
    loop 0

  let rec to_bexpr = function
    |  Asgn {func; arg = (x,w); body} -> 
      let open Expr in 
      let e = var (Var.make x w) in
      BExpr.((func $ e) == body)
    | Cond (phi, rst) -> 
      BExpr.imp [phi; to_bexpr rst]
    | And ts -> List.map ts ~f:to_bexpr |> BExpr.ands

  let action_atoms x (f, i, o) : (BExpr.t Stream.t) lazy_t = 
    let open BExpr in 
    let open Expr in 
    assert (Var.width x = i);
    let action = (Var.make f o) $ var x in 
    let constraints = lazy (
      Stream.count_to ~n:o
      |> Stream.map ~f:(fun a -> 
        if a = o then
          action >= bvi a o 
        else
          action == bvi a o
    )) in
    constraints

  let action_assigns x (f, i, o) : asgn Stream.t =
    assert (Var.width x = i);
    let func = (f, o) in
    let arg = Var.str x, Var.width x in  
    Stream.count_to ~n:o
    |> Stream.map ~f:(fun a -> {func; arg; body = Expr.bvi a o})
  
  let is_action (f,_,_) = 
    String.is_suffix f ~suffix:"$action"

  let partition_actions = 
    List.partition_tf ~f:is_action

  let fgets f x e = 
    let open BExpr in 
    let open Expr in 
    (f $ var x) == (TyGuS.to_expr e)

  let atoms funs = 
    let open Stream in
    of_list funs
    |> bind ~f:(fun (f,i,o) ->
      let x = Var.make "x" i in
      (TyGuS.tygus_stream [("x",i)] funs o 
      |> Stream.map ~f:(fgets (Var.make f o) x))
      @ if is_action (f,i,o) then 
          action_atoms x (f,i,o)
        else lazy Nil
    )
    
  let shuffle xs =
    List.map xs ~f:(fun x -> (x, Random.int 1000))
    |> List.sort ~compare:(fun (_, i) (_, j) -> Int.compare i j)
    |> List.map ~f:Tuple2.get1

  let bexpr_synth n funs = 
    let atoms = atoms funs in
    let rec loop n  = 
      if n <= 0 then 
        atoms
      else
        let open Stream in 
        let open BExpr in 
        let rst = loop (n-1) in 
        prod rst rst
        |> bind ~f:(fun (phi, psi) -> 
          [ors;ands;imp]
          |> List.map ~f:(fun ctor -> ctor [phi;psi])
          |> of_list)
    in
    Stream.count_to ~n
    |> Stream.bind ~f:loop

  let cond_synth abstract_funs target_funs : t Stream.t = 
    let abs_acts, _ = partition_actions abstract_funs in 
    let streams : t Stream.t list = 
      let open Stream in 
      List.map target_funs ~f:(fun (f,i,o) ->
        let x = Var.make "x" i in
        let abstract_atoms = 
          List.filter_map abs_acts ~f:(fun g -> 
            if Tuple3.get2 g = i then 
              Some (Lazy.force (action_atoms x g))
            else
              None
          ) |> ndoveprod |> map ~f:BExpr.ands
        in
        if is_action (f,i,o) then
          action_assigns x (f,i,o)
          |> doveprod abstract_atoms
          |> map ~f:(fun (atom, a) -> Cond (atom, Asgn a))
        else
          (TyGuS.tygus_stream ["x",i] abstract_funs o 
            |> map ~f:(fun e -> Asgn {func = (f, o); arg = ("x",i); body = TyGuS.to_expr e}))
          |> doveprod abstract_atoms
          |> map ~f:(fun (atom, e) -> Cond (atom, e))
    ) in
    Stream.ndoveprod streams
    |> Stream.map ~f:(fun ss -> And ss)

  let ite guard tru fls = 
    let open Gpl.BExpr in 
    ands [
      imp [guard; tru];
      imp [not_ guard; fls];
    ]

  let assignments ~from ~to_ =
    let open Stream in 
    bind (of_list from) ~f:(fun (f,i,o) -> 
      filter_map (of_list to_) ~f:(fun (g, i', o') ->
        if i = i' && o = o' && String.(f <> g) then
          let open BExpr in 
          let open Expr in 
          let f = Var.make f o in 
          let g = Var.make g o in 
          let x = var (Var.make "x" i) in 
          Some ((f $ x) == (g $ x))
        else
          None
      )
    )

  let setlike_add xs ys ~equal = 
    List.fold ys ~init:xs ~f:(fun output y ->
      if List.mem output y ~equal then 
        output
      else
        output@[y]
    )

  let conjunctions atoms n =
    let open Stream in 
    Printf.printf "conjunctions %d\n%!" n; 
    let rec loop i =
      Printf.printf "loop %d \n%!" i;
      if i <= 0 then 
        Nil
      else if i <= 1 then
        let+ a = atoms in 
        Printf.printf "An atom!\n%!";
        [a]
      else 
        let* alpha = atoms in 
        let* phi = loop (i - 1) in
        Printf.printf "Constructing %s && %s\n%!" (BExpr.to_smtlib alpha) (BExpr.(to_smtlib (ands phi)));
        if List.mem phi alpha ~equal:BExpr.equal then 
          Nil
        else
          return (alpha::phi)
        
        (* let* r_budget = count_to ~n:(n-1) in
        let* l_budget = count_to ~n:(n - 1 - r_budget) in
        let* phis = loop l_budget in 
        let* psis = loop r_budget in
        (* let* phis = loop (n-1) in 
        let* psis = loop (n-1) in *)
        let phis' = setlike_add phis psis ~equal:BExpr.equal in
        if List.is_empty phis' then
          Nil
        else 
          return phis' *)
    in
    let+ phis = loop n in 
    BExpr.ands phis



  let ite_synth read_funs write_funs = 
    let open Stream in
    let actions = assignments ~from:read_funs ~to_:write_funs in 
    assert (not (is_empty actions));
    let conjs n = 
      Printf.printf "Getting conjunctions up to %d\n%!" n;
      count_to ~n >>= conjunctions actions 
    in 
    let rec loop budget =
      Printf.printf "BUDGET:%d\n%!" budget;
      let prefix = conjs budget in 
      assert (not (is_empty prefix));
      prefix @ lazy (
        Printf.printf "ITE BUDGET %d\n%!" budget; 
        if budget > 1 then 
          let budget = budget - 1 in 
          let* grd_cost = count_to ~n:budget in
          let* tru_cost = count_to ~n:(budget - grd_cost) in
          let  fls_cost = budget - tru_cost in 
          let* grd = bexpr_synth grd_cost read_funs in
          let* tru = conjs tru_cost in
          let+ fls = loop fls_cost in 
          ite grd tru fls
        else 
          Nil
      )
    in
    let* i = nats in
    loop i
    

  let synth_streams abstract_funs target_funs = 
    let streams = 
      List.map target_funs ~f:(fun (f, i, o) -> 
        let open BExpr in 
        let x = Var.make "x" i in
        let f = Var.make f o in 
        TyGuS.tygus_stream ["x", i] abstract_funs o
        |> Stream.map ~f:(fun e -> Forall(x, Expr.(f $ var x) == TyGuS.to_expr e))
      )
    in
    streams
    |> Stream.ndoveprod
    |> Stream.map ~f:BExpr.ands
end

module FormGen = MakeForm (BVExpr)

let testF () = 
  FormGen.synth_streams [
    "LAG", 32, 32;
    "NEXT", 32, 9
  ] [
    "FWD", 32, 9
  ]

let action_decompose () = 
  FormGen.synth_streams [
    "Eth", 48, 9;
    "IPAct", 32, 1;
    "IPPort", 32, 9;
    "IPDst", 32, 48;
    "Vld", 16, 1;
  ] [
    "Eth'", 48, 9;
    "FwdAct", 32, 1;
    "WriteAct", 32, 1;
    "FwdPort", 32, 9;
    "WriteDst", 32, 48;
    "Vld", 16, 1;
  ]

let show = Stream.take_and_print ~to_string:Gpl.BExpr.to_smtlib

let normalize_fun (x, ins) = 
  let open Gpl in 
  match ins with 
  | [i] ->
    (Var.str x, i, Var.width x)
  | _ -> failwith "unrecognized number of arguments"

let normalize_funs (fs : (Gpl.Var.t * int list) list) : (string * int * int) list = 
  let compare (x, _, _) (y, _, _) = String.compare x y in
  List.map fs ~f:normalize_fun
  |> List.dedup_and_sort ~compare


let init_search pre abs tgt pst = 
  let open Gpl in 
  let abs_form = SygusGen.vcgen abs [] pst in 
  let abs_funs = BExpr.get_funs abs_form |> normalize_funs in
  let ver_cnsq = SygusGen.vcgen tgt [] abs_form in 
  Printf.printf "Product VC: \n %s \n%!" (BExpr.to_smtlib ver_cnsq);
  let all_funs = BExpr.get_funs ver_cnsq |> normalize_funs in 
  let tgt_funs = List.filter all_funs ~f:(Fn.non (List.mem abs_funs ~equal:(fun (x, _, _) (y, _, _) -> String.(x = y)))) in
  abs_funs, tgt_funs, begin fun mapping -> 
    Printf.printf "-------------------+\n%s\n----------------------+\n%!" (BExpr.to_smtlib mapping);
    SMT.satisfiable mapping &&
    BExpr.(imp [quantify `All mapping; pre; ver_cnsq]
      |> SMT.verify)
  end

(** [phi |==> psi] returns true when phi is strictly stronger than psi. that is
  [phi => psi] and [not (psi => phi)]*)
let ( |==> ) phi psi =
  let open Gpl.BExpr in
  ands [
    imp [phi; psi];
    not_ (imp [psi; phi])
  ] |> SMT.verify

let synthesize gas pre abs tgt pst =
  let abs_funs, tgt_funs, is_correct = init_search pre abs tgt pst in 
  FormGen.ite_synth abs_funs tgt_funs
  |> Stream.take gas
  |> List.find ~f:is_correct