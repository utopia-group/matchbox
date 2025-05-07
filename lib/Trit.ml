open Core

module Trit = struct
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

  let overlap a b =
    match a, b with 
    | T, F | F, T -> false
    | _, _ -> true

  let equal a b = 
    match a, b with 
    | T, T | F, F | U, U -> true
    | _,_ -> false

  let to_string = function 
    | T -> "1"
    | F -> "0"
    | U -> "*"

  let of_string s = 
    match s with 
    | "0" -> F
    | "1" -> T
    | "*" -> U
    | _ -> failwithf "unrecognized ternary bitstring %s" s ()

  let denote = function 
    | T -> Bit.Set.true_
    | F -> Bit.Set.false_
    | U -> Bit.Set.either_

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

  let adder c a b =
    match c, a, b with
    | F, F, F -> [F,F]
    | F, F, T | F, T, F | T, F, F -> [F,T]
    | F, T, T | T, F, T | T, T, F -> [T,F]
    | F, U, U | U, F, U | U, U, F -> [F,F; F,T; T,F] (* EVERYTHING BUT (T,T)*)
    | U, F, T | F, U, T | F, T, U -> [T,F; F,T] (* EVERYTHING BUT (T,T), (F,F)*)
    | U, F, F | F, U, F | F, F, U -> [F,U]
    | T, T, T -> [T,T]
    | T, U, U | U, T, U | U, U, T  -> [F,T; T,F; T,T](* EVERYTHING MINUS (F,F)*)
    | U, T, F | T, U, F | T, F, U -> [T,F; F,T] (* EVERYTHING MINUS (T,T), (F,F)*)
    | U, T, T | T, U, T | T, T, U -> [T,U] (* EVERYTHING MINUS (F,F), (F,T) *)
    | U, U, U -> [U,U]

  let maskify = function 
  | F -> U
  | T -> T
  | U -> failwith "unexpected * in Trit.maskify operation"

  let get_bit_exn = function 
  | F -> false
  | T -> true
  | U -> failwith "tried to get bit from * trit"

end

module Vector = struct 
  type t = Trit.t List.t
  let to_string bs = 
    List.map bs ~f:(Trit.to_string) 
    |> String.concat ~sep:""

  let bitstring_of_hexchar c = 
    let i = String.of_char c |> (^) "0x" |> Int.of_string in 
    let str b = if b then "1" else "0" in 
    List.init 4 ~f:(fun j -> str ((1 lsl j) = Int.(i land (1 lsl j)))) 
    |> List.rev
    |> String.concat

  
  let hexstring_to_bitstring hexstring =
    String.fold hexstring ~init:"" ~f:(fun acc hex_char -> 
      acc ^ bitstring_of_hexchar hex_char
    )

  let of_string bs = 
    let prefix = String.prefix bs 2 in 
    let cleaned_to_ternary = 
      String.fold ~init:[] ~f:(fun acc b -> 
        acc @ [Trit.of_string (Char.to_string b)]
      )
    in
    match prefix with 
    | "0b" | "#b" -> 
      String.chop_prefix_exn bs ~prefix |> cleaned_to_ternary
    | "0x" | "#x" -> 
      String.chop_prefix_exn bs ~prefix
      |> hexstring_to_bitstring
      |> cleaned_to_ternary      
    | "00" | "01" | "10" | "11" -> 
      (* if the first two characters are bits, assume its a bv*)
      cleaned_to_ternary bs
    | _ -> failwithf "unrecognized tv %s" bs ()

  let to_bitmask tv : Bit.Vector.t * Bit.Vector.t =
    let open Trit in 
    List.map tv ~f:(function 
      | T -> (true, true)
      | F -> (false, true)
      | U -> (false, false) (* could also be true, false, but this is cannoncial*)
      )
    |> List.unzip

  let equal = List.equal Trit.equal
  let length : t -> int = List.length

  let denote bv : Bit.VectorSet.t = 
    List.fold bv ~init:(Bit.VectorSet.singleton []) ~f:(fun vset bexp -> 
      let bs = Trit.denote bexp |> Bool.Set.elements in
      Bit.VectorSet.elements vset
      |> List.bind ~f:(fun vector -> 
        List.map bs ~f:(fun b ->
        vector @ [b]  
      ))
      |> Bit.VectorSet.of_list
    )

  let overlap = List.for_all2_exn ~f:Trit.overlap

  let not : t -> t = List.map ~f:Trit.not

  let ( && ) = List.map2_exn ~f:Trit.(&&)
  let ( || ) = List.map2_exn ~f:Trit.(||)
  let ( ^ ) = List.map2_exn ~f:Trit.(^)

  let ( + ) xs ys : Trit.t list list =
    let (let+) xs f = List.map xs ~f in 
    let (let*) xs f = List.bind xs ~f in 
    List.fold2_exn (List.rev xs) (List.rev ys) ~init:([Trit.F, []]) ~f:(fun acc x y ->
      let* c, bs = acc in
      let+ c', s = Trit.adder c x y in 
      (c', s::bs)  
    ) |> List.map ~f:snd

  let maskify = (* turns 0s into *s *)
    List.map ~f:Trit.maskify

  let from_mask_pair value mask =
    value && (maskify mask)

  let rec random n = 
    if n <= 0 then 
      []
    else
      Trit.random () :: random (n - 1)

  let eq_pres1 (exp : t) ~(f : Bit.Vector.t -> Bit.Vector.t) ~(g :t -> t) = 
    let values = Bit.VectorSet.map (denote exp) ~f in
    let exp' = g exp in
    denote exp'
    |> Bit.VectorSet.equal values 

  let eq_pres2 (exp1 : t) (exp2 : t) ~(f : Bit.Vector.t -> Bit.Vector.t -> Bit.Vector.t) ~(g:t -> t -> t) : bool =
    let values = Bit.VectorSet.cartesian_map (denote exp1) (denote exp2) ~f in
    let exp' = g exp1 exp2 in
    denote exp'
    |> Bit.VectorSet.equal values
end

include Trit