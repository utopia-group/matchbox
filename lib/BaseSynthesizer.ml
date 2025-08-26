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

(* Module for TransformExpr synthesis *)
module TransformKey = struct
  module T = struct
    type t = BaseLogic.TransformExpr.t

    let compare = Poly.compare
    let sexp_of_t expr = Sexp.Atom (BaseLogic.TransformExpr.to_string expr)

    let t_of_sexp _sexp =
      failwith "t_of_sexp not implemented for TransformExpr.t"
  end

  include T
  include Comparable.Make (T)
end

(* Synthesis function for TransformExpr.t *)
let synth_transform ?(max_depth = 3) (phi : SurfaceLogic.t -> bool) :
    SurfaceLogic.t list =
  (* Symbol universe *)
  let symbols : Symbol.t list =
    List.init 32 ~f:(fun i -> Symbol.make (sprintf "F%d" i) [] 0)
  in

  let mk_transform_logic symbol expr : SurfaceLogic.t =
    SurfaceLogic.{defined = symbol; definition = expr}
  in

  (* Generate seed expressions using the new TransformExpr syntax *)
  let seeds : SurfaceLogic.t list =
    let ids =
      List.map symbols ~f:(fun f ->
          mk_transform_logic f (TransformExpr.table_symbol f))
    in
    let invs =
      List.map symbols ~f:(fun f ->
          mk_transform_logic f
            (TransformExpr.invert (TransformExpr.table_symbol f)))
    in
    (* Add basic cross-compositions to seeds *)
    let basic_compositions =
      List.concat_map symbols ~f:(fun target ->
          List.concat_map symbols ~f:(fun s1 ->
              List.filter_map symbols ~f:(fun s2 ->
                  if
                    Symbol.compare s1 s2 = 0
                    || Symbol.compare target s1 = 0
                    || Symbol.compare target s2 = 0
                  then None
                  else
                    let s1_symbol = TransformExpr.table_symbol s1 in
                    let s2_symbol = TransformExpr.table_symbol s2 in
                    Some
                      (mk_transform_logic target
                         (TransformExpr.compose s1_symbol s2_symbol)))))
    in
    ids @ invs @ basic_compositions
  in

  let dedup_by_transform_key (xs : SurfaceLogic.t list) : SurfaceLogic.t list =
    fst
      (List.fold_right xs
         ~init:([], Set.empty (module TransformKey))
         ~f:(fun p (acc, ps) ->
           if Set.mem ps p.definition then (acc, ps)
           else (p :: acc, Set.add ps p.definition)))
  in

  let expand_transform (p : SurfaceLogic.t) : SurfaceLogic.t list =
    let f = p.defined in
    let base_symbol = TransformExpr.table_symbol f in

    let base =
      [
        mk_transform_logic f base_symbol;
        mk_transform_logic f (TransformExpr.invert base_symbol);
        mk_transform_logic f (TransformExpr.project base_symbol []);
        mk_transform_logic f (TransformExpr.rename_keys base_symbol []);
        mk_transform_logic f (TransformExpr.rename_actions base_symbol []);
        mk_transform_logic f (TransformExpr.write_data base_symbol []);
        mk_transform_logic f (TransformExpr.write_key base_symbol []);
      ]
    in

    let comps_rebound =
      List.concat_map symbols ~f:(fun d ->
          if Symbol.compare d f = 0 then []
          else
            let g_symbol = TransformExpr.table_symbol d in
            [
              mk_transform_logic d (TransformExpr.compose base_symbol g_symbol);
              mk_transform_logic d (TransformExpr.compose g_symbol base_symbol);
            ])
    in

    let joins =
      List.map symbols ~f:(fun g ->
          let g_symbol = TransformExpr.table_symbol g in
          mk_transform_logic f (TransformExpr.join base_symbol g_symbol []))
    in

    base @ comps_rebound @ joins
  in

  depth := 0;

  let scan_layer (layer : SurfaceLogic.t list) : SurfaceLogic.t list =
    List.filter layer ~f:phi
  in

  let seen0 =
    Set.of_list
      (module TransformKey)
      (List.map seeds ~f:(fun p -> p.definition))
  in
  let sols0 = scan_layer seeds in
  if not (List.is_empty sols0) then (
    printf "Transform synthesis depth reached: %d\n%!" !depth;
    sols0)
  else if max_depth = 0 then failwith "Depth limit reached"
  else
    let rec grow (current_layer : SurfaceLogic.t list)
        (seen : Set.M(TransformKey).t) : SurfaceLogic.t list =
      depth := !depth + 1;
      if !depth > max_depth then failwith "Depth limit reached";
      let grown =
        current_layer
        |> List.concat_map ~f:expand_transform
        |> dedup_by_transform_key
        |> List.filter ~f:(fun p -> not (Set.mem seen p.definition))
      in
      if List.is_empty grown then failwith "Search space exhausted";
      let seen' =
        List.fold grown ~init:seen ~f:(fun acc p -> Set.add acc p.definition)
      in
      let sols = scan_layer grown in
      if not (List.is_empty sols) then (
        printf "Transform synthesis depth reached: %d\n%!" !depth;
        sols)
      else (
        if !depth = max_depth then failwith "Depth limit reached";
        grow grown seen')
    in
    grow seeds seen0
