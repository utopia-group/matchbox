open Core


module BitSet = struct
  type t = Bool.Set.t
  let true_ = Bool.Set.singleton true
  let false_ = Bool.Set.singleton false
  let either_ = Bool.Set.of_list [true;false]
  let neither_ = Bool.Set.of_list [true]

  let map ~f : t -> t = Bool.Set.map ~f

  let map2_exn a b ~f = 
    let as_ = Bool.Set.elements a in 
    let bs_ = Bool.Set.elements b in 
    List.map2_exn as_ bs_ ~f
    |> Bool.Set.of_list

  let not = map ~f:(not)
  
  let ( && ) = map2_exn ~f:(&&)

  let ( || ) = map2_exn ~f:(||)
  
end


module BitVector = struct
  type t = bool list
  let compare = List.compare Bool.compare
  
  let t_of_sexp = List.t_of_sexp Bool.t_of_sexp

  let sexp_of_t = List.sexp_of_t Bool.sexp_of_t

  
  let ( ^ ) = 
    let ( ^ ) a b = (a || b) && not (a && b) in
    List.map2_exn ~f:(^)
  
  
  let not : t -> t = List.map ~f:(not)
  let ( && ) = List.map2_exn ~f:(&&)
  let ( || ) = List.map2_exn ~f:(||)

end

module VectorSet = struct 
  include Set.Make (BitVector)
  let cartesian_map ~f a b =
    let xs = elements a in
    let ys = elements b in 
    List.bind xs ~f:(fun x -> 
      List.map ys ~f:(fun y -> 
        f x y
      )  
    )
    |> of_list

end

module Ternary = struct
  type t = 
    | T
    | F
    | U

  let random () =
    match Random.int 3 with
    | 0 -> T
    | 1 -> F
    | 2 -> U
    | _ -> failwith "impossible"


  let equal a b = 
    match a, b with 
    | T, T | F, F | U, U -> true
    | _,_ -> false

  let to_string = function 
    | T -> "1"
    | F -> "0"
    | U -> "*"

  let denote : t -> BitSet.t = function 
    | T -> BitSet.true_
    | F -> BitSet.false_
    | U -> BitSet.either_

  let ( && ) a b = 
    match a, b with 
    | F, _ | _, F -> F
    | T, c | c, T -> c
    | U, U -> U
  
  let ( || ) a b = 
    match a, b with 
    | T, _ | _, T -> T
    | F, c | c, F -> c
    | U, U -> U

  let not a = 
    match a with 
    | T -> F
    | F -> T
    | U -> U

  let ( ^ ) a b = 
     match a, b with 
     | T, F | F, T -> T
     | T, T | F, F -> F
     | _, _ -> U

end


type t = Ternary.t List.t
let to_string bs = 
  List.map bs ~f:(Ternary.to_string) 
  |> String.concat ~sep:""

let denote bv : VectorSet.t = 
  List.fold bv ~init:VectorSet.empty ~f:(fun vset bexp -> 
    let bs = Ternary.denote bexp |> Bool.Set.elements in
    VectorSet.elements vset
    |> List.bind ~f:(fun vector -> 
      List.map bs ~f:(fun b ->
      vector @ [b]  
    ))
    |> VectorSet.of_list
  )

let not : t -> t = List.map ~f:Ternary.not

let ( && ) = List.map2_exn ~f:Ternary.(&&)
let ( || ) = List.map2_exn ~f:Ternary.(||)
let ( ^ ) = List.map2_exn ~f:Ternary.(^)


let rec random n = 
  if n <= 0 then 
    []
  else
    Ternary.random () :: random (n - 1)



let eq_pres1 (exp : t) ~(f : BitVector.t -> BitVector.t) ~(g :t -> t) = 
  let values = VectorSet.map (denote exp) ~f in
  let exp' = g exp in
  denote exp'
  |> VectorSet.equal values 

let eq_pres2 (exp1 : t) (exp2 : t) ~(f : BitVector.t -> BitVector.t -> BitVector.t) ~(g:t -> t -> t) : bool =
  let values = VectorSet.cartesian_map (denote exp1) (denote exp2) ~f in
  let exp' = g exp1 exp2 in
  denote exp'
  |> VectorSet.equal values
