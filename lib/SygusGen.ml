open Core
open Gpl
open SyGuS

let terminal_state p = 
  GPL.free_vars p 
  |> Set.fold ~init:BExpr.true_ ~f:(fun phi x -> 
    let x' = Var.make ("$$" ^ Var.str x) (Var.width x) in
    BExpr.and_ phi @@
    BExpr.(Expr.var x == Expr.var x')
  )

let vcgen_lifted (p : GPL.t) (phi : BExpr.t): Var.t List.t * BExpr.t = 
  let open GPL in 
  let rec wp phi : GPL.t -> (Var.t list * BExpr.t) = function
  | Prim p -> begin
    match p with 
    | Table {name; keys; actions}-> begin
      let inputs = List.mapi keys ~f:(fun i (x,_) -> 
        let varname = Printf.sprintf "%s$%s$%d" name (Var.str x) i in
        Var.make varname (Var.width x)
      ) in
      let action_choice = 
        Var.make (Printf.sprintf "%s$action" name) (List.length actions)
      in 
      let actions = 
        List.mapi actions ~f:(fun i (params, cmds) ->
          let assignments = 
            List.map params ~f:(fun param -> 
              let arg = Var.make (Printf.sprintf "%s$%d$%s" name i (Var.str param)) (Var.width param) in
              (param, arg)
            )
          in
          let new_vars = List.map ~f:(Tuple2.get2) assignments in 
          let prefix = List.map assignments ~f:(fun (p, a) -> Primitives.Action.assign p @@ Expr.var a) in 
          let ( =~= ) = if i + 1 = List.length actions then BExpr.(>=) else BExpr.(==) in 
          let precond = GPL.sequence [
            assume Expr.(var action_choice =~= Expr.bvi i (List.length actions));
            prefix @ cmds
            |> GPL.action_to_gpl
          ] |> wp phi |> Tuple2.get2 in
          (new_vars, precond)
        )
      in
      let new_action_vars = List.bind ~f:(Tuple2.get1) actions in 
      let action_wps = List.map ~f:(Tuple2.get2) actions |> BExpr.ands in 
      let assumption = 
        BExpr.ands @@
        List.map2_exn keys inputs ~f:(fun (key, _) input -> 
          BExpr.(Expr.var key == Expr.var input)  
        )
      in
      (inputs @ [action_choice] @ new_action_vars,
        BExpr.(imp [assumption; action_wps]))
      end
    | Active (Assign (x,e)) -> 
      ([], BExpr.subst x e phi)
    | Active (Passive (Assert psi)) ->
      ([], BExpr.and_ psi phi)
    | Active (Passive (Assume psi)) -> 
      ([], BExpr.imp [psi; phi])
  end
  | Seq cs -> 
    List.fold_right cs ~init:([],phi) ~f:(fun c (xs, phi) -> 
      let ys, psi = wp phi c in
      (xs @ ys, psi)
    )
  | Choice cxs ->  
    List.fold ~init:([], BExpr.false_) ~f:(fun (xs, psis) c -> 
      let (ys, psi) = wp phi c in
      (xs @ ys, BExpr.ors [psis; psi])
    ) cxs
  in
  wp phi p


let get_pieces x = Var.str x |> String.split ~on:'$'
let get_table_name x = get_pieces x |> List.hd_exn

let is_decimal_str i = 
  try String.(i = (Int.of_string i |> Int.to_string))
  with Failure _ -> false

let get_outputs abs_vars = 
  let f x = 
    match get_pieces x with 
    | [_; "action"] -> true 
    | [_;i;_] -> is_decimal_str i
    | _ -> 
      failwithf "unrecognized variable naming convention %s" (Var.str x) ()
  in
  List.filter abs_vars ~f

let get_same_inputs abs_vars x =
  let x_table_name = get_table_name x in 
  let f y = 
    match get_pieces y with 
    | [table_name; _; i] when String.(table_name = x_table_name) -> is_decimal_str i
    | _ -> false

  in
  List.filter abs_vars ~f

let reconstruct_invocations abs_vars : (Var.t * Var.t list) list = 
  let outputs = get_outputs abs_vars in 
  let inputs = get_same_inputs abs_vars in 
  List.map outputs ~f:(fun o -> 
    let varname = Var.str o in 
    let funname = Var.make (String.capitalize varname) (Var.width o) in 
    (funname, inputs o)
  )

let vcgen (p : GPL.t) (obs_vars : Var.t List.t) (phi : BExpr.t): BExpr.t = 
  let rec wp phi p =
    let open GPL in 
    match p with 
    | Prim p -> 
      begin match p with 
      | Active (Assign (x,e)) -> 
        BExpr.subst x e phi
      | Active (Passive (Assume psi)) -> 
        BExpr.imp [psi; phi]
      | Active (Passive (Assert psi)) -> 
        BExpr.and_ psi phi
      | Table {name; keys; actions;} -> 
        let actwidth = List.length actions in 
        let function_args = List.map ~f:(Expr.var) (obs_vars @ List.map ~f:Tuple2.get1 keys) in 
        let function_name = String.capitalize name in
        let action_is idx : BExpr.t = 
          let f = Var.make (Printf.sprintf "%s$action" function_name) actwidth in
          let ( =~= ) = if idx + 1 = List.length actions then BExpr.( >= ) else BExpr.( == ) in
          Expr.(f $* function_args  =~=  bvi idx actwidth)
        in
        let data x = 
          let f = Var.make (Printf.sprintf "%s$data$%s"  function_name (Var.str x)) (Var.width x) in
          Expr.(f $* function_args)
        in
        let encode_action act ~withargs:xs =
          GPL.(seq
            (sequence_map xs ~f:(fun x -> assign x (data x)))
            (sequence_map act ~f:GPL.active)
          )
          |> wp phi
        in
        List.mapi actions ~f:(fun idx (args, act) ->
          BExpr.(imp [
            action_is idx;
            encode_action act ~withargs:args
          ])
        )
        |> BExpr.ands
        
      end
      | Seq cs -> 
        List.fold_right cs ~init:phi ~f:(fun c phi -> wp phi c)
      | Choice cxs ->  
        List.map ~f:(wp phi) cxs |> BExpr.ors
      in
  wp phi p

let bv_grammar ~width ~over = 
  let start = Var.make "Start" width in 
  Grammar.{
    nonterminals = [start];
    productions = Production.[
      {symbol = start; 
       options = List.concat [
          List.filter_map over ~f:(fun x -> 
            if Var.width x = width then 
              Some (Expr.var x)
            else 
              None
            );
       ]
      }
    ] 
   }


let gen_fun ((f : Var.t), (args : Var.t List.t))  : SynthFun.t = 
  (* [abstract_vars] is the list of variables from the abstract program we can use to construct the function*)
  (* [f] is the function we're synthesizing *)
  (* [args] is the list of variables we'll pass into f*)
  {
    symbol = f;
    variables = args;
    grammar = bv_grammar ~width:(Var.width f) ~over:args
  }

let uniq ~equal xs =
  let rec uniq' xs seen =
    match xs with 
    | [] -> seen
    | x::xs ->
      if List.exists seen ~f:(equal x) then 
        uniq' xs seen
      else
        uniq' xs (x::seen)
  in
  uniq' xs []
  
let invocations (phi : BExpr.t) : (Var.t * Var.t list) List.t= 
  let rec invocations_expr =
    let open Expr in 
    function
    | BV _ | Var _ -> []
    | UnOp (_, e) -> invocations_expr e
    | BinOp(_, e1, e2) -> invocations_expr e1 @ invocations_expr e2
    | Apply(f, ws, es) -> 
      let params = List.mapi ws ~f:(fun i w -> Var.make (Printf.sprintf "x$%d" i) w) in
      (f, params) :: List.bind es ~f:invocations_expr 
  in
  let rec invocations' = 
    let open BExpr in 
    function 
    | TFalse | TTrue -> []
    | TComp (_, e1, e2) -> invocations_expr e1 @ invocations_expr e2
    | TNary (_, phis) -> 
      List.bind ~f:invocations' phis 
    | TNot phi | Forall(_,phi) | Exists(_,phi) ->
      invocations' phi
  in
  invocations' phi
  |> uniq ~equal:(fun (x,_) (y,_) -> Var.equal x y) 

let gen_funs = List.map ~f:gen_fun

let ( ==> ) phi psi = BExpr.imp [phi; psi]

let migrate (source : GPL.t) (target : GPL.t) (pre : BExpr.t) (post : BExpr.t) : string = 
  let obs_vars, phi = vcgen_lifted source post in 
  let phi = vcgen target obs_vars phi in
  let invocations = invocations phi in 
  let sygus = { 
    funs = gen_funs invocations;
    variables = Set.to_list (BExpr.free_vars phi);
    constraints = [pre ==> phi];
  } in 
  let solutions = SyGuS.run "/usr/bin/cvc5 --lang=sygus" sygus |> Solution.extract in
  List.map ~f:(Solution.pretty_print obs_vars (reconstruct_invocations obs_vars)) solutions
  |> String.concat ~sep:"\n"
  