open Core

let ( ^ ) a b = (a || b) && not (a && b)

module Set = struct 
  type t = Bool.Set.t

  let singleton b = Bool.Set.singleton b
  let true_ = singleton true
  let false_ = singleton false

  let union = Bool.Set.union

  let either_ = union true_ false_

end


module Vector = struct
  type t = bool list

  let of_string (bs : string) =
    let rec loop bs =
      let n = String.length bs in 
      if n = 0 then 
        [] 
      else
        let b = String.get bs 0 in 
        let bs' = String.drop_prefix bs 1 in 
        match b with 
        | '0' -> false :: loop bs'
        | '1' -> true :: loop bs'
        | _ -> failwithf "unrecognized character %c in bitstring %s" b bs ()
    in
    match String.slice bs 0 1 with 
    | "0b" | "#b" -> 
      loop (String.drop_prefix bs 2)
    | _ -> loop bs

  let length : t -> int = List.length

  let to_string bs = 
    List.map bs ~f:(fun b -> 
      if b then "1" else "0"  
    ) |> String.concat ~sep:""

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

  let ( ^ ) = 
    List.map2_exn ~f:(^)

  let not : t -> t = List.map ~f:(not)
  let ( && ) = List.map2_exn ~f:(&&)
  let ( || ) = List.map2_exn ~f:(||)



end

module VectorSet = struct 
  include Core.Set.Make (Vector)
  let cartesian_map ~f a b =
    let xs = elements a in
    let ys = elements b in 
    List.bind xs ~f:(fun x -> 
      List.map ys ~f:(fun y -> 
        f x y
      )  
    )
    |> of_list

  let to_string bs= 
    fold bs ~init:"" ~f:(fun acc bv -> 
      String.(acc ^ (if acc = "" then "" else ",") ^ Vector.to_string bv)) 
    |> Printf.sprintf "{%s}"

  let union_map xs ~f =
    List.fold xs ~init:empty ~f:(fun set x -> 
      union set (f x)
    )

  let prepend bs a = 
    fold a ~init:empty ~f:(fun acc vector -> 
      union_map bs ~f:(fun a -> singleton (a :: vector))
      |> union acc
    )
end
