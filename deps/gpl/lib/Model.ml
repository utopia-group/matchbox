open Core

type t = (Bigint.t * int) Map.M(Var).t

let to_string model =
  Map.fold model ~init:"" ~f:(fun ~key ~data ->
      Printf.sprintf "  %s = (_ bv%s %d)\n%s"
        (Var.str key)
        (Bigint.to_string (fst data))
        (snd data)
    )
  |> Printf.sprintf "{\n%s}\n"

let empty : t = Map.empty (module Var)

let update m x v =
  Map.set m ~key:x ~data:v

let lookup m x = Map.find m x

let disjoint_union m1 m2 =
  Map.merge m1 m2
    ~f:(fun ~key:_ -> function
        | `Left x | `Right x ->
          Some x
        | `Both _ ->
          failwith "union not disjoint"
      )

let of_alist_exn alist = Map.of_alist_exn (module Var) alist

let of_map m = m
