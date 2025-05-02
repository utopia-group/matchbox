open Core 

type 'a t = 
  | Out of 'a
  | DontCare of 'a t
  | Branch of {tru: 'a t; fls: 'a t}

type bdd = bool t
let accept : bdd = Out true
let rec reject n : bdd = 
  if n <= 0 then 
     Out false
  else 
    DontCare (reject (n - 1))

type add = string t


let rec of_tv (tv : Trit.Vector.t) = 
  let open Trit in
  let depth = Vector.length tv in 
  match tv with 
  | [] -> accept
  | tern::tv -> 
    let diagram = of_tv tv in 
    match tern with 
    | T -> 
      Branch {tru = diagram; fls = reject (depth - 1)}
    | F -> 
      Branch {fls = diagram; tru = reject (depth - 1)};
    | U -> 
      DontCare diagram

let of_matchstring str = 
  Trit.Vector.of_string str
  |> of_tv

let to_ternary (diagram : bdd) : Trit.Vector.t list * Trit.Vector.t list = 
  let open Trit in 
  let cons_all (t : t) : Vector.t list -> Vector.t list = List.map ~f:(List.cons t) in
  let stringify tvs = List.map tvs ~f:Vector.to_string |> String.concat ~sep:"," |> Printf.sprintf "\"%s\"" in 
  let rec loop path diag : Vector.t list * Vector.t list = 
    match diag with 
    | Out true -> ([path], [])
    | Out false -> ([], [path])
    | DontCare d -> 
      let acc, rej = loop path d in
      Printf.printf "Adding * to %s and %s\n%!" (stringify acc) (stringify rej);
      cons_all U acc,
      cons_all U rej
    | Branch {tru;fls} -> 
      let tacc, trej = loop path tru in 
      let facc, frej = loop path fls in
      let acc = cons_all T tacc @ cons_all F facc in 
      let rej = cons_all T trej @ cons_all F frej in 
      let rej = List.(filter rej ~f:(fun tv -> exists acc ~f:(Vector.overlap tv))) in 
      Printf.printf "Adding 1 to %s and %s\n%!" (stringify tacc) (stringify facc);
      Printf.printf "Adding 0 to %s and %s\n%!" (stringify trej) (stringify frej);
      acc, rej
    in 
    loop [] diagram

let denote d : Bit.VectorSet.t =
  let rec loop bvs d = 
    match d with
    | Out true -> (bvs, Bit.VectorSet.empty)
    | Out false -> (Bit.VectorSet.empty, bvs)
    | Branch {tru; fls} -> 
      let taccept, treject = loop (Bit.VectorSet.prepend [true] bvs) tru in
      let faccept, freject = loop (Bit.VectorSet.prepend [false] bvs) fls in 
      Bit.VectorSet.union taccept faccept,
      Bit.VectorSet.union treject freject
    | DontCare g -> 
      let accept, reject = loop bvs g in 
      Bit.VectorSet.prepend [false;true] accept,
      Bit.VectorSet.prepend [false;true] reject
  in 
  let accept, reject = loop (Bit.VectorSet.singleton []) d in 
  Bit.VectorSet.diff accept reject


let rec negate = function
  | Out b -> Out (not b)
  | DontCare d -> 
    DontCare (negate d)
  | Branch {tru;fls} -> 
    Branch {
      tru = negate tru;
      fls = negate fls
    }

let rec ( && ) bdd bdd' =
  match bdd, bdd' with 
  | Out false, _ | _, Out false -> Out false
  | Out true, b | b, Out true -> b
  | DontCare b,  DontCare b' ->
    DontCare (b && b')
  | Branch g, Branch g' -> 
    Branch {
      tru = g.tru && g'.tru;
      fls = g.fls && g'.fls;
    }
  | DontCare b, Branch g | Branch g, DontCare b -> 
    Branch {
      tru = g.tru && b;
      fls = g.fls && b;
    }

let rec ( || ) d d' =
  match d, d' with 
  | Out true, _ | _, Out true -> Out true
  | Out false, b | b, Out false -> b
  | DontCare d, DontCare d' -> 
    DontCare (d || d')
  | DontCare b, Branch g | Branch g, DontCare b ->
    Branch {
      tru = g.tru || b;
      fls = g.fls || b;
    }
  | Branch g, Branch g' -> 
    Branch {
      tru = g.tru || g'.tru;
      fls = g.fls || g'.fls;
    }

let ( - ) d d' = d && negate d'

let rec partial_add d obs : 'a option t =
  match d with 
  | Out true -> Out (Some obs)
  | Out false -> Out None
  | DontCare d -> DontCare (partial_add d obs)
  | Branch g -> 
    Branch {
      tru = (partial_add g.tru obs);
      fls = (partial_add g.fls obs);
    }

let rec ( |?> ) (partial : 'a option t) (total : 'a t) = 
    match partial, total with 
    | Out (Some a), _ -> Out a
    | Out None, Out a -> Out a
    | DontCare d, DontCare d' -> 
      DontCare (d |?> d')
    | DontCare d, Branch {tru;fls} -> 
      Branch {
        tru = d |?> tru;
        fls = d |?> fls;
      }
    | Branch {tru;fls}, DontCare d -> 
      Branch {
        tru = tru |?> d;
        fls = fls |?> d;
      }
    | Branch p, Branch t -> 
      Branch {
        tru = p.tru |?> t.tru;
        fls = p.fls |?> t.fls;
      }
    | Out _, Branch _ | Out _, DontCare _ | Branch _, Out _ | DontCare _, Out _ -> 
      failwith "decision diagrams were different sizes"


let add_bdd_to_add (d' : 'a t) (d, obs) =
  partial_add d obs |?> d'

let get_paths (add : 'a t) = 
  let open Trit in 
  let rec loop diag (tv : Vector.t) : (Vector.t * 'a) list = 
    match diag with 
    | Out obs -> [(tv,  obs)]
    | DontCare d ->
      (tv @ [U])
      |> loop d 
    | Branch {tru;fls} ->
      let tpaths = loop tru (tv @ [T]) in 
      let fpaths = loop fls (tv @ [F]) in 
      tpaths @ fpaths
  in
  loop add []

let bdds_to_add (bdds : (bdd * 'a) list) (def : 'a) : 'a t =
  List.rev bdds
  |> List.fold ~init:(Out def) ~f:add_bdd_to_add