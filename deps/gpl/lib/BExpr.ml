open Core
type bop =
  | LAnd
  | LOr
  | LArr
  | LIff
  [@@deriving eq]

let bop_to_smtlib = function
  | LAnd -> "and"
  | LOr -> "or"
  | LArr -> "=>"
  | LIff -> "="

type comp =
  | Eq
  | Ult
  | Ule
  | Uge
  | Ugt
  | Slt
  | Sle
  | Sgt
  | Sge
  [@@deriving eq]
  
let comp_to_smtlib = function
  | Eq -> "="
  | Ult -> "bvult"
  | Ule -> "bvule"
  | Uge -> "bvuge"
  | Ugt -> "bvugt"
  | Slt -> "bvslt"
  | Sle -> "bvsle"
  | Sgt -> "bvsgt"
  | Sge -> "bvsge"
  [@@deriving eq]

type t = 
  | TFalse
  | TTrue
  | TNot of t
  | TNary of bop * t list
  | TComp of comp * Expr.t * Expr.t
  | Forall of Var.t * t
  | Exists of Var.t * t
  [@@deriving eq]

let false_ = TFalse
let true_ = TTrue
let not_ phi = TNot phi
let ands phis = 
  match phis with 
  | [phi] -> phi 
  | _ -> 
    let phis = List.bind phis ~f:(function 
      | TNary (LAnd, psis) -> psis
      | phi -> [phi]
      ) in 
    TNary (LAnd, phis)
let and_ phi psi = ands [phi; psi]
let ors phis = 
  let phis = List.bind phis ~f:(function
    | TNary (LOr, psis) -> psis
    | phi -> [phi]
  ) in
  TNary (LOr, phis)
let imp phis = TNary(LArr, phis)
let iff phis = TNary (LIff, phis)
let forall x phi = Forall(x,phi)
let exists x phi = Exists(x, phi)

let forall_ xs phi = 
  List.fold xs ~init:phi ~f:(Fn.flip forall)

let exists_ xs phi = 
  List.fold xs ~init:phi ~f:(Fn.flip exists)

let ( == ) e1 e2 = TComp(Eq, e1, e2)
let ( >= ) e1 e2 = TComp(Uge, e1, e2)
let ( <= ) e1 e2 = TComp (Ule, e1, e2)
let ( > ) e1 e2 = TComp (Ugt, e1, e2)
let ( < ) e1 e2 = TComp (Ult, e1, e2)
let ( >=! ) e1 e2 = TComp(Sge, e1, e2)
let ( <=! ) e1 e2 = TComp (Sle, e1, e2)
let ( >! ) e1 e2 = TComp (Sgt, e1, e2)
let ( <! ) e1 e2 = TComp (Slt, e1, e2)

let ( $=$ ) (f,ws) (g, ls) = 
  assert (List.equal (=) ws ls);
  assert (Var.width f = Var.width g);
  let xs = List.mapi ws ~f:(fun i -> Var.make (Printf.sprintf "x%d" i)) in
  let es = List.map xs ~f:Expr.var in
  let phi = 
    let open Expr in 
    (f $* es) == (g $* es)
  in
  forall_ xs phi

let rec to_smtlib_buffer indent buff b : unit =
  let space = Util.space (2 * indent) in
  Buffer.add_string buff space;
  match b with
  | TFalse ->
      Buffer.add_string buff "false"
  | TTrue ->
      Buffer.add_string buff "true"
  | TNot (t) ->
      Buffer.add_string buff "(not";
      to_smtlib_buffer 0 buff t;
      Buffer.add_string buff ")";
  | TNary (b,ts) ->
      Buffer.add_string buff "(";
      Buffer.add_string buff (bop_to_smtlib b);
      List.iter ts ~f:(fun t1 ->
          Buffer.add_string buff "\n";         
          to_smtlib_buffer (indent + 1) buff t1;
        );
      Buffer.add_string buff ")";
  | TComp (comp, e1, e2) ->
      Buffer.add_string buff "(";
      Buffer.add_string buff (comp_to_smtlib comp);
      Buffer.add_string buff " ";
      Buffer.add_string buff (Expr.to_smtlib e1);
      Buffer.add_string buff " ";     
      Buffer.add_string buff (Expr.to_smtlib e2);
      Buffer.add_string buff ")"
  | Forall (v, t) ->
      Buffer.add_string buff (Printf.sprintf "(forall (%s)\n" (Var.list_to_smtlib_quant [v]));
      to_smtlib_buffer (indent+1) buff t;
      Buffer.add_string buff ")"
  | Exists (v, t) ->
      Buffer.add_string buff (Printf.sprintf "(exists (%s)\n" (Var.list_to_smtlib_quant [v]));
      to_smtlib_buffer (indent+1) buff t;
      Buffer.add_string buff ")"


let to_smtlib phi =
  let b = Buffer.create 8000 in
  to_smtlib_buffer 0 b phi;
  Buffer.contents b

let eval_comp c (v1,_) (v2,_) =
  match c with
  | Eq  -> Bigint.(=)  v1 v2
  | Ult -> Bigint.(<)  v1 v2
  | Ule -> Bigint.(<=) v1 v2
  | Uge -> Bigint.(>=) v1 v2
  | Ugt -> Bigint.(>)  v1 v2
  | Slt -> Bigint.(<)  v1 v2
  | Sle -> Bigint.(<=) v1 v2
  | Sgt -> Bigint.(>)  v1 v2
  | Sge -> Bigint.(>=) v1 v2
      
let rec eval_op op bs : bool =
  match op with
  | LAnd -> List.for_all   bs ~f:Fn.id
  | LOr  -> List.exists    bs ~f:Fn.id
  | LIff -> List.all_equal bs  ~equal:Bool.equal
            |> Option.is_some
  | LArr ->
    match List.rev bs with
    | []  -> failwith "cannot compute => of empty list"
    | [_] -> failwith "cannot compute => of singleton list"
    | b::bs ->
      (*=> bs b ==== (/\bs) => b ==== b \/ ~(/\bs) *)
      b || not (eval_op LAnd bs)

let rec eval (model : Model.t) (phi : t) : bool =
  match phi with
  | TFalse -> false
  | TTrue -> true
  | TComp (c, e1, e2) ->
    let v1 = Expr.eval model e1 |> Result.ok_or_failwith in
    let v2 = Expr.eval model e2 |> Result.ok_or_failwith in
    begin match c with
      | Eq ->
        let b = eval_comp c v1 v2 in
        b
      | _ -> eval_comp c v1 v2
    end
  | TNary (op, bs) ->
    List.map ~f:(eval model) bs
    |> eval_op op
  | TNot b ->
    let v = eval model b in
    not v
  | Forall _  | Exists _ ->
    failwith "Dont have evaluation for quantifiers"


let subst (x : Var.t) e : t -> t = 
  let rec subst' = function
    | TFalse -> TFalse
    | TTrue -> TTrue
    | TComp (c, e1, e2) -> 
      TComp (c, Expr.subst x e e1, Expr.subst x e e2)
    | TNary (op, phis) ->
      TNary (op, List.map ~f:subst' phis )
    | TNot phi -> TNot (subst' phi)
    | Forall (y, phi) ->
      if Var.equal y x then
        Forall (y, phi)
      else 
        Forall (y, subst' phi)
    | Exists (y, phi) -> 
      if Var.equal y x then 
        Exists (y, phi)
      else 
        Exists (y, subst' phi)
  in
  subst'

let rec free_vars =
  let open Var.Set in
  function
  | TFalse -> empty
  | TTrue -> empty
  | TComp (_, e1, e2) -> 
    Set.union (Expr.vars e1) (Expr.vars e2)
  | TNary (_, phis) -> 
    union_list @@ List.map ~f:free_vars phis
  | TNot phi -> free_vars phi
  | Forall (x, phi) | Exists (x,phi) -> 
    Set.remove (free_vars phi) x

let quantify how phi = 
  let xs = free_vars phi |> Set.to_list in
  match how with 
  | `All -> forall_ xs phi
  | `Exists -> exists_ xs phi

let rec get_funs phi = 
  match phi with
  | TTrue -> []
  | TFalse -> []
  | TNot phi | Forall(_, phi) | Exists(_, phi) -> get_funs phi
  | TNary (_, phis) -> List.bind phis ~f:get_funs
  | TComp (_, e1, e2) -> Expr.get_funs e1 @ Expr.get_funs e2


let rec size phi = 
  match phi with 
  | TTrue | TFalse -> 1
  | TNot phi -> 1 + size phi
  | Forall(_, phi) | Exists(_,phi) ->  2 + size phi
  | TNary(_, phis) -> List.sum (module Int) phis ~f:size
  | TComp (_, e1, e2) -> Expr.size e1 + 1 + Expr.size e2
      