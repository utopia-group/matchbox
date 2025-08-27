open Core
open BaseLogic

let depth = ref (-1)

module Key = struct
  module T = struct
    type t = BaseLogic.t

    let sexp_of_t = BaseLogic.sexp_of_t
    let t_of_sexp = BaseLogic.t_of_sexp
    let compare = BaseLogic.compare
  end

  include T
  include Comparable.Make (T)
end

let synth ?(max_depth = 3) (phi : t -> bool) : t list =
  (* Symbol universe *)
  let symbols : Symbol.t list =
    List.init 32 ~f:(fun i -> Symbol.make (sprintf "F%d" i) [] 0)
  in

  let mk f def : t = {defined = f; definition = def} in

  let seeds : t list =
    let ids = List.map symbols ~f:(fun f -> mk f (Clause.Id f)) in
    let invs = List.map symbols ~f:(fun f -> mk f (Clause.Invert f)) in
    ids @ invs
  in

  let dedup_by_key (xs : t list) : t list =
    fst
      (List.fold_right xs
         ~init:([], Set.empty (module Key))
         ~f:(fun p (acc, ps) ->
           if Set.mem ps p then (acc, ps) else (p :: acc, Set.add ps p)))
  in

  let expand (p : t) : t list =
    let f = p.defined in
    let base =
      [
        mk f (Clause.MapOut (f, ActionTfx.Project []));
        mk f (Clause.MapIn (f, MatchTfx.Project []));
        mk f (Clause.Id f);
        mk f (Clause.Invert f);
      ]
    in
    let comps_rebound =
      List.concat_map symbols ~f:(fun d ->
          if Symbol.compare d f = 0 then []
          else List.map symbols ~f:(fun g -> mk d (Clause.Compose (f, g))))
    in
    let joins = List.map symbols ~f:(fun g -> mk f (Clause.Join (f, g, []))) in
    base @ comps_rebound @ joins
  in

  depth := 0;

  let scan_layer (layer : t list) : t list = List.filter layer ~f:phi in

  let seen0 = Set.of_list (module Key) seeds in
  let sols0 = scan_layer seeds in
  if not (List.is_empty sols0) then (
    printf "Depth reached: %d\n%!" !depth;
    sols0)
  else if max_depth = 0 then failwith "Depth limit reached"
  else
    let rec grow (current_layer : t list) (seen : Set.M(Key).t) : t list =
      depth := !depth + 1;
      if !depth > max_depth then failwith "Depth limit reached";
      let grown =
        current_layer |> List.concat_map ~f:expand |> dedup_by_key
        |> List.filter ~f:(fun p -> not (Set.mem seen p))
      in
      if List.is_empty grown then failwith "Search space exhausted";
      let seen' = List.fold grown ~init:seen ~f:Set.add in
      let sols = scan_layer grown in
      if not (List.is_empty sols) then (
        printf "Depth reached: %d\n%!" !depth;
        sols)
      else (
        if !depth = max_depth then failwith "Depth limit reached";
        grow grown seen')
    in
    grow seeds seen0
