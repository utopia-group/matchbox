open Core

let ( ^ ) a b = (a || b) && not (a && b)

module Set = struct 
  type t = Bool.Set.t

  let singleton b = Bool.Set.singleton b
  let true_ = singleton true
  let false_ = singleton false

  let union a b = Bool.Set.union_list [a; b]

  let either_ = union true_ false_

end


module Vector = struct
  type t = bool list [@@deriving sexp, compare]

  let of_string (bv : string) =
    let rec loop bs =
      match bs with
      | [] -> []
      | b0 :: b1 :: bs' when Char.(b0 = '0' || b0 = '#') && Char.(b1 = 'b') ->
        loop bs'
      | b :: bs' ->
        (match b with 
        | '0' -> false
        | '1' -> true
        | _ -> failwithf "unrecognized character %c in bitstring %s" b bv ())
        :: loop bs'
    in
    loop (String.to_list bv)

  let length : t -> int = List.length

  let of_int ~width i =
    let rec loop w i =
      if w <= 0 then 
        []
      else 
        loop (w-1) (i lsr 1) @ [i mod 2 = 1]
    in 
    if width < 0 then 
      failwith "cannot create negative-width bitvector"
    else 
      let i' = i mod Float.to_int (2. ** Float.of_int width) in 
      loop width i'

  let zero w : t =
    List.init w ~f:(fun _ -> false)

  let ones w : t =
    List.init w ~f:(fun _ -> true)

  let one w : t =
    if w < 1 then 
      failwith "cannot create bitvector of value 1 with fewer than 1 bit"
    else 
      zero (w - 1) @ [true]


  let to_string bs = 
    List.map bs ~f:(fun b -> 
      if b then "1" else "0"  
    ) |> String.concat ~sep:""

  let to_int bs = String.concat["0b"; to_string bs] |> Int.of_string

  let enumerate width =
    let rec loop w =
      if w <= 0 then
        [[]]
      else
        let smaller = loop (w - 1) in
        List.bind smaller ~f:(fun bits ->
          [false :: bits; true :: bits]
        )
    in
    loop width

  let random ?(seed = None) width =
    Option.iter seed ~f:Random.init;
    List.init width ~f:(fun _ -> Random.bool ())

  let compare = List.compare Bool.compare
  let equal = List.equal Bool.equal
  
  let t_of_sexp = List.t_of_sexp Bool.t_of_sexp

  let sexp_of_t = List.sexp_of_t Bool.sexp_of_t
  
  let ( + ) xs ys = 
    List.fold2_exn (List.rev xs) (List.rev ys) ~init:(false, []) ~f:(fun (c, bs) x y ->
        let s = c ^ (x ^ y) in
        let c = (x && y) || (c && (x ^ y)) in
        (c, s::bs)
    ) |> snd

  let incr xs = 
    let w = List.length xs in 
    xs + one w

  let decr xs =
    let w = List.length xs in 
    xs + ones w

  let ( ^ ) = 
    List.map2_exn ~f:(^)

  let not : t -> t = List.map ~f:(not)
  let ( && ) = List.map2_exn ~f:(&&)
  let ( || ) = List.map2_exn ~f:(||)



end

(* module VectorSet = struct 
  include Core.Set.Make (Vector)
  let cartesian_map ~f a b =
    let xs = Core.Set.elements a in
    let ys = Core.Set.elements b in 
    List.bind xs ~f:(fun x -> 
      List.map ys ~f:(fun y -> 
        f x y
      )  
    )
    |> of_list

  let to_string bs= 
    Core.Set.fold bs ~init:"" ~f:(fun acc bv -> 
      String.(acc ^ (if acc = "" then "" else ",") ^ Vector.to_string bv)) 
    |> Printf.sprintf "{%s}"

  let union_map xs ~f =
    List.fold xs ~init:empty ~f:(fun set x -> 
      Core.Set.union set (f x)
    )

  let prepend bs a = 
    Core.Set.fold a ~init:empty ~f:(fun acc vector -> 
      union_map bs ~f:(fun a -> singleton (a :: vector))
      |> Core.Set.union acc
    )
end *)


module VectorSet = struct 
  include Core.Set.Make (Vector)

  let elements = Core.Set.elements
  let union = Core.Set.union
  let diff = Core.Set.diff

  let cartesian_map ~f a b =
    let xs = Core.Set.elements a in
    let ys = Core.Set.elements b in 
    List.bind xs ~f:(fun x -> 
      List.map ys ~f:(fun y -> 
        f x y
      )  
    )
    |> of_list

  let to_string bs= 
    Core.Set.fold bs ~init:"" ~f:(fun acc bv -> 
      String.(acc ^ (if acc = "" then "" else ",") ^ Vector.to_string bv)) 
    |> Printf.sprintf "{%s}"

  let union_map xs ~f =
    List.fold xs ~init:empty ~f:(fun set x -> 
      Core.Set.union set (f x)
    )

  let prepend bs a = 
    Core.Set.fold a ~init:empty ~f:(fun acc vector -> 
      union_map bs ~f:(fun a -> singleton (a :: vector))
      |> Core.Set.union acc
    )
end