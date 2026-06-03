open Core
open BaseLogic
module T = Type 
module R = ResourceBaseChecker
module F = FDBaseChecker.DepFunDep
module L = BaseLogic

type t = {
    vars : int String.Map.t;
    typs : T.ctx;
    rscs : R.ctx;
    gfds : F.itfc_spec;
    assertions: F.itfc_spec;
    prog : L.t list;
    props : Property.t list;
    stats : Stats.t
}

let empty = {
    vars = String.Map.empty;
    typs = String.Map.empty;
    rscs = String.Map.empty;
    gfds = String.Map.empty;
    assertions = String.Map.empty;
    prog = [];
    props = [];
    stats = Stats.empty;
}

let (@) (p1 : t) (p2 : t) : t= 
    { vars = Map.merge p1.vars p2.vars ~f:(fun ~key -> function
        | `Left v | `Right v -> Some v
        | `Both (v1, v2) ->
          if v1 = v2 then Some v1
          else failwithf "Variable %s has contradictory widths: %d vs. %d" key v1 v2 ()
      );
      typs = T.(p1.typs @ p2.typs);
      rscs = R.(p1.rscs @ p2.rscs);
      gfds = F.(p1.gfds @ p2.gfds);
      assertions = F.(p1.assertions @ p2.assertions);
      prog = p1.prog @ p2.prog;
      props = p1.props @ p2.props;
      stats = Stats.(p1.stats + p2.stats);
    }

let add_property (prop : Property.t) (p : t) : t =
  {p with props = List.append p.props [prop]}

let concat : t list -> t = 
    List.fold ~init:empty ~f:(@)

let add_vars (vars : int String.Map.t) (p : t) : t = 
  {p with 
      vars = Map.merge p.vars vars ~f:(fun ~key -> function
        | `Left v | `Right v -> Some v
        | `Both (v1, v2) ->
          if v1 = v2 then Some v1
          else failwithf "Variable %s has contradictory widths: %d vs. %d" key v1 v2 ()
      )
  }

let add_type (tbl : string) (tau : T.t) (p : t) : t = 
  {p with 
      typs = Map.add_exn p.typs ~key:tbl ~data:tau;
      gfds = Map.add_multi p.gfds ~key:tbl ~data:(F.fd_of_typ tau)
  }

let add_assertion (tbl : string) (fd : F.t) (p : t) : t =
  {p with assertions = Map.add_multi p.assertions ~key:tbl ~data:fd}

let rec elim_override (clause : Clause.t) =
  match clause with
  | Table _ -> clause
  | Override (c1, c2, typ) -> (
    match elim_override c1, elim_override c2 with
    | Table (name1, mat1, _), Table (_, mat2, _) ->
      Table (name1, List.append mat1 mat2, typ)
    | _ -> failwith "unreachable")
  | _ -> failwith "unimplemented"

let is_total keys (clause : Clause.t) =
  match clause with
  | Table (_, mat, _) ->
    Map.for_alli keys
      ~f:(fun ~key ~data ->
        let has_catchall =
          let catch_all = Trit.Vector.wc data in
          List.exists mat ~f:(fun {matches; _} ->
            match Map.find_exn matches key with
            | Ternary tv -> Trit.Vector.equal tv catch_all
            | _ -> false)
        in
        if has_catchall then true
        else
          let fully_enumerated =
            let enumerated = List.fold mat ~init:(Set.empty (module Int))
              ~f:(fun acc {matches; _} ->
                match Map.find_exn matches key with
                | Exact bv -> Set.add acc (Bit.Vector.to_int bv)
                | _ -> acc)
            in
            Set.length enumerated = 1 lsl data
          in
          fully_enumerated)
  | _ -> failwith "unreachable"

let check_assertion {defined; definition} (p : t) : t =
  {p with
   gfds =
   match Map.find p.assertions (Symbol.to_string defined) with
   | Some assertions ->
     assertions 
     |> List.map ~f:(fun stmt ->
        if definition |> elim_override |> is_total stmt.source then stmt
        else failwithf "Assertion failed: %s must satisfy %s" 
          (Symbol.to_string defined) (F.to_string stmt) ())
     |> List.fold ~init:p.gfds ~f:(fun acc fd ->
        Map.add_multi acc ~key:(Symbol.to_string defined) ~data:fd)
   | None -> p.gfds
  }

let refine_fds (p : t) : t = 
  let open FDBaseChecker in
  {p with
   gfds = Map.map p.gfds ~f:(fun fds ->
    fds
    |> List.sort ~compare:DepFunDep.compare
    |> List.fold ~init:[] ~f:(fun acc fd ->
      if List.exists acc
        ~f:(fun fd' -> DepFunDep.compare fd fd' >= 0)
      then acc
      else fd :: acc))
  }

let rec complete_clause (clause : Clause.t option) (table : string) (typ : T.t)
  : Clause.t option =
  let open Semantics in
  Option.map clause ~f:(fun c ->
    match c with
    | Table (_, t, c_typ) ->
      Clause.Table (table,
        List.map t ~f:(fun ma ->
          MatchAction.{
            ma with
            hw = typ.hw;
            matches =
            (* TODO: typecheck here? *)
            List.cartesian_product
              (Map.to_alist ma.matches)
              (Map.to_alist typ.keys)
            |> List.fold ~init:(Map.empty (module String))
                ~f:(fun acc ((_, match_), (key, width)) ->
                  if Match.length match_ = width then
                    Map.set acc ~key ~data:match_
                  else acc);
            data =
            (* TODO: typecheck here? *)
            List.cartesian_product
              (Map.to_alist ma.data)
              (Map.to_alist typ.data)
            |> List.fold ~init:(Map.empty (module String))
                ~f:(fun acc ((_, bv), (key, width)) ->
                  if Bit.Vector.length bv = width then
                    Map.set acc ~key ~data:bv
                  else acc)
          }
        ), c_typ)
    | MapIn (c', WildCard x, c_typ) ->
      let w = Map.find_exn typ.keys (Var.str x) in
      let completed_c' = Option.value_exn (complete_clause (Some c') table typ) in
      MapIn (completed_c', WildCard (Var.make (Var.str x) w), c_typ)
    | MapIn (c', tfx, c_typ) -> 
      let completed_c' = Option.value_exn (complete_clause (Some c') table typ) in
      MapIn (completed_c', tfx, c_typ)
    | MapOut (c', tfx, c_typ) -> 
      let completed_c' = Option.value_exn (complete_clause (Some c') table typ) in
      MapOut (completed_c', tfx, c_typ)
    | Override (c1, c2, c_typ) ->
      let c1' = Option.value_exn (complete_clause (Some c1) table typ) in
      let c2' = Option.value_exn (complete_clause (Some c2) table typ) in
      Override (c1', c2', c_typ)
    | _ -> c
  )

let rec fill_var_widths_expr expr keys =
  let open Gpl.Expr in
  match expr with
  | Var (s, w) when w = -1 ->
    let w' = Map.find_exn keys s in
    Var (s, w')
  | BinOp (bop, expr1, expr2) ->
    BinOp (bop,
      fill_var_widths_expr expr1 keys,
      fill_var_widths_expr expr2 keys)
  | _ -> expr

let rec fill_var_widths_bexpr bexpr keys =
  let open Gpl.BExpr in
  match bexpr with
  | TComp (comp, expr1, expr2) ->
    TComp (comp,
      fill_var_widths_expr expr1 keys,
      fill_var_widths_expr expr2 keys)
  | TNary (bop, bexprs) ->
    TNary (bop, List.map bexprs ~f:(fun e -> fill_var_widths_bexpr e keys))
  | _ -> bexpr

let fill_var_widths (p : t) : t =
  {p with gfds =
   Map.mapi p.gfds ~f:(fun ~key ~data ->
     List.map data ~f:(fun fd ->
       let keys = (Map.find_exn p.typs key).keys in
       {fd with refine = fill_var_widths_bexpr fd.refine keys}
     )
   )
  }

let create_table rows =
  let open Semantics in
  Clause.table ""
    (List.map rows ~f:(fun (keys, action, data) ->
      MatchAction.make TCAM
        (keys
         |> List.mapi ~f:(fun i bv ->
            (Int.to_string i, bv |> Trit.Vector.of_string |> Match.Ternary))
         |> Map.of_alist_exn (module String))
        (MagmaAction.make action)
        (data
         |> List.mapi ~f:(fun i bv ->
            (Int.to_string i, Bit.Vector.of_string bv))
         |> Map.of_alist_exn (module String))
      )
    )

let bulk_create_table decls keys action data =
  let open Semantics in
  let enums, uniques = List.partition_tf decls
    ~f:(function (_, "enumerate", _) -> true
               | (_, "unique", _) -> false
               | _ -> failwith "expected either 'enumerate' or 'unique'")
  in
  enums
  (* Generate all combinations of 'enumerate' fields *)
  |> List.fold ~init:[Map.empty (module String)]
    ~f:(fun acc (x, _, w) ->
      List.map (List.cartesian_product acc (Bit.Vector.enumerate w))
        ~f:(fun (row, a) -> Map.set row ~key:x ~data:a))
  (* Extend each combination with unique values of 'unique' fields *)
  |> List.fold 
    ~init:([], List.fold uniques ~init:(Map.empty (module String))
      ~f:(fun acc (x, _, _) -> Map.set acc ~key:x ~data:0))
    ~f:(fun (rows, seen) row ->
      let row', seen' =
        List.fold uniques
          ~init:(row, seen)
          ~f:(fun (row, seen) (x, _, w) ->
            let idx = Map.find_exn seen x in
            let data = Bit.Vector.of_int ~width:w idx in
            Map.set row ~key:x ~data, Map.set seen ~key:x ~data:(idx + 1))
      in
      row' :: rows, seen')
  |> fst
  (* Make match-action rules *)
  |> List.map ~f:(fun row ->
    MatchAction.make TCAM
      (Map.of_alist_exn
        (module String)
        (List.map keys ~f:(fun k -> k, Match.exact (Map.find_exn row k))))
      (MagmaAction.make action)
      (Map.of_alist_exn
        (module String)
        (List.map data ~f:(fun k -> k, Map.find_exn row k))))
  |> Clause.table ""

let opt_add_def (defined : Symbol.t) (clause : Clause.t option) (p : t) : t =
  match clause with
  | None -> p
  | Some definition -> 
      {p with 
          prog = List.append p.prog [{defined; definition}]
      }

let add_resource_limit table_name limit (p : t) : t= 
  {p with 
    rscs = Map.update p.rscs table_name ~f:(function
      | None -> limit
      | Some other_limit -> Int.min limit other_limit 
    )
  }

let add_gfd table_name gfd (p : t) : t = 
  {p with 
    gfds = Map.update p.gfds table_name ~f:(function
      | None -> [gfd]
      | Some old_gfds -> gfd::old_gfds
    );
    stats = {p.stats with num_fds = p.stats.num_fds + 1;
                          size_fds = p.stats.size_fds + F.size gfd}
  }

let set_typecheck_time t (p : t) : t = 
  {p with
    stats = {p.stats with
      typetime = t
    }
  }

let update_stats clause (p : t) : t =
  match clause with 
  | None -> p
  | Some clause ->
    let stats = Stats.analyze clause in
    {p with 
      stats = Stats.(p.stats + stats) 
    } 


let well_formed ctx (stmt : BaseLogic.t) =
  let annotated = BaseChecker.infer ctx.typs stmt in
  let table_name = Symbol.to_string stmt.defined in 
  let expected_type = Map.find_exn ctx.typs table_name in
  let computed_type = Clause.typeof_exn annotated in
  if not Type.(equal expected_type computed_type) then 
    failwithf "Expected table %s to have type:\n\t%s\nbut it had type:\n\t%s" 
      table_name 
      (Type.to_string expected_type)
      (Type.to_string computed_type) () 
  else
    {defined = stmt.defined; definition = annotated}

let functional ctx ({defined;definition} : BaseLogic.t) = 
  let requirements = Map.find_exn ctx.gfds (Symbol.to_string defined) in
  let had_type_error = ref false in
  List.iter requirements ~f:(fun gfd ->
    let new_spec = F.check ctx.gfds ctx.vars definition gfd in
    let spec = F.remaining_obligations ctx.gfds new_spec in
    Map.iteri spec ~f:(fun ~key ~data ->
      List.iter data ~f:(fun fd ->
        Printf.eprintf "Type Error: %s must satisfy %s\n" key (F.to_string fd);
        had_type_error := true;
      )
    )
  );
  if !had_type_error then failwith "error in the gFD type system";
  {defined;definition}

let appropriately_sized ctx {defined;definition}  = 
  let name = Symbol.to_string defined in 
  match Map.find ctx.rscs name with 
  | None -> {defined;definition}
  | Some maximum ->
    let bound = R.calculate_max_cost ctx.rscs definition in
    if bound > maximum then
      failwithf "table %s supports only %d rules, but its definition could produce %d"
        name maximum bound ()
    else {defined;definition}
      
let typecheck (ctx : t) : t = 
  let c = Clock.start () in
  let prog = 
    List.fold ctx.prog ~init:(ctx, []) ~f:(fun (ctx, prog) matchstick -> 
      well_formed ctx matchstick
      |> functional ctx
      |> appropriately_sized ctx
      |> Fn.flip (List.cons) prog
      |> Tuple2.create (check_assertion matchstick ctx)
    ) |> snd |> List.rev
  in
  let typetime = Clock.stop c in
  {ctx with prog;
            stats = {ctx.stats with typetime}}