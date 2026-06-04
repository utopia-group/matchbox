open Core

module T = struct
  type t = String.t * int [@@deriving hash, compare, sexp, equal]

  let make s i : t =
    if String.length s = 0 then
      failwith "Variable cannot have length 0"
    else (s,i)

  let str : t -> String.t = Tuple2.get1
  let width : t -> int = Tuple2.get2

  let to_smtlib_quant ((s,i) : t ) : string =
    Printf.sprintf "(%s (_ BitVec %d))" s i

  let list_to_smtlib_quant : t list -> string =
    List.fold ~init:""
      ~f:(fun acc v -> Printf.sprintf "%s%s " acc (to_smtlib_quant v))

  let to_smtlib_decl ((s, i) : t) : string =
    Printf.sprintf "(declare-const %s (_ BitVec %d))\n" s i

  let list_to_smtlib_decls : t list -> string =
    List.fold ~init:"\n"
      ~f:(fun acc v -> Printf.sprintf "%s%s" acc (to_smtlib_decl v))
end

include T
include Comparable.Make (T)
