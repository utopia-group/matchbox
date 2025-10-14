open Core
open Gpl
open BaseLogic
module DepFunDep = struct 
  type t = {
    refine : BExpr.t;
    source : int String.Map.t;
    target : int String.Map.t;
  }

  let compare fd1 fs2 =
    let fd1_source_keys = Map.key_set fd1.source in
    let fd2_source_keys = Map.key_set fs2.source in
    if Set.equal fd1_source_keys fd2_source_keys then (
      let fd1_target_keys = Map.key_set fd1.target in
      let fd2_target_keys = Map.key_set fs2.target in
      if Set.equal fd1_target_keys fd2_target_keys then 0
      else if Set.is_subset fd1_target_keys ~of_:fd2_target_keys then -1
      else 1)
    else if Set.is_subset fd1_source_keys ~of_:fd2_source_keys then -1
    else 1

  let to_string {refine; source; target} =
    let aux xs = 
      Map.to_alist xs
      |> List.map ~f:(fun (name, width) -> 
        Printf.sprintf "%s : %i" name width  
      )
      |> String.concat ~sep:", "
    in
    Printf.sprintf 
      "{%s | %s} ---> {%s}"
      (aux source)
      (BExpr.to_smtlib refine)
      (aux target)

  let fd_eq fd1 fd2 = 
    BExpr.equal fd1.refine fd2.refine
    && Map.equal (=) fd1.source fd2.source
    && Map.equal (=) fd1.target fd2.target

  let size {source;target;refine} =
    Map.length source + Map.length target + BExpr.size refine  

  type itfc_spec = t list String.Map.t 

  let (@) (phi : itfc_spec) (psi : itfc_spec) : itfc_spec =
    Map.merge phi psi ~f:(fun ~key:_ -> function
      | `Left fds | `Right fds -> Some fds 
      | `Both (fds1, fds2) -> 
        Some (fds1 @ fds2)
    )

  let fd_of_table_type table_type =
    let data_types = Type.get_data table_type in 
    let key_types = Type.get_keys table_type in 
    { refine = BExpr.true_;
      source = Map.of_alist_exn (module String) key_types;
      target = data_types;
    }
 

  let fd_of_typ typ = 
    fd_of_table_type typ

  let inherent_fd (gamma : Type.ctx) (f : Symbol.t) : t =
    Type.find_exn gamma (Symbol.to_string f)
    |> fd_of_typ


  let find_fd (spec : itfc_spec) (table : string) = 
    Map.find spec table

  let implies (spec : itfc_spec) (table : string) (fd : t) = 
    Option.value_map (find_fd spec table) 
      ~default:false
      ~f:(List.exists ~f:(fun fd' ->
        BExpr.equal fd.refine fd'.refine
        && Map.equal (=) fd.source fd'.source
        && (
          Map.fold2 ~init:true fd.target fd'.target ~f:(fun ~key:_ ~data acc -> 
            match data with
            | `Left _ -> false
            | `Right _ -> acc
            | `Both (w1, w2) -> if w1 = w2 then acc else false
          )
        )
      ))

  let union = Map.merge ~f:(fun ~key -> function 
    | `Left w | `Right w -> Some w
    | `Both (w1, w2) -> 
      if w1 = w2 then 
        Some w1
    else 
      failwithf "union failed on key %s" key ()
  ) 

  let diff (m1 : itfc_spec) (m2 : itfc_spec) : itfc_spec = 
    Map.filter_keys m1 ~f:(fun k -> 
      not (Map.mem m2 k)  
    )

  let remaining_obligations (known : itfc_spec) (required : itfc_spec) : itfc_spec = 
    Map.mapi required ~f:(fun ~key ~data -> 
      List.filter data ~f:(Fn.non (implies known key))
    )



  let var_set (m : int String.Map.t) : Var.Set.t = 
    Map.fold m ~init:Var.Set.empty ~f:(fun ~key ~data acc -> 
      Set.add acc (Var.make key data)
    ) 

  let map_of_varlist xs = 
    List.fold xs ~init:String.Map.empty ~f:(fun acc x -> 
      Map.add_exn acc ~key:(Var.str x) ~data:(Var.width x)
    )

  let map_of_varset xs = 
    Set.to_list xs |> map_of_varlist

  let rec check (ctx : itfc_spec) (clause : Clause.t) (goal : t) : itfc_spec =
    let open Clause in 
    match clause with 
    | Id (f, _) -> 
      Map.add_multi ctx ~key:f.name ~data:goal
    | Table (_, _, None) -> 
      failwith "Must run base type interpreter before FDChecker"
    | Table (_, _, Some typ) -> 
      assert (fd_eq (fd_of_typ typ) goal);
      ctx
    | Join (c1, c2, _) -> 
      let goal1 = fd_of_table_type (typeof_exn c1) in 
      let goal2 = fd_of_table_type (typeof_exn c2) in 
      assert (Map.(equal (=) goal.source (union goal1.source goal2.source)));
      assert (Map.(equal (=) goal.target (union goal1.target goal2.target)));
      assert (Set.is_subset (BExpr.free_vars goal.refine) ~of_:(var_set goal1.source));
      assert (Set.is_subset (BExpr.free_vars goal.refine) ~of_:(var_set goal2.target));
      let rgoal1 = {goal1 with refine = goal.refine } in 
      let rgoal2 = {goal2 with refine = goal.refine } in
      check (check ctx c1 rgoal1) c2 rgoal2
    | Override (_f, _g, _) ->
      failwith "TODO"
    | Compose (before, after, _) -> 
      let goal_before = fd_of_table_type (typeof_exn before) in 
      let goal_after = fd_of_table_type (typeof_exn after) in 
      assert (Set.equal (Map.key_set goal_before.target) (Map.key_set goal_after.source));
      let refined_goal_before = {goal_before with refine = goal.refine} in 
      check (check ctx before refined_goal_before) after goal_after
    | MapOut(c, Project xs, _) ->
      assert (Map.(equal (=) (map_of_varlist xs) goal.target));
      check ctx c goal
    | MapOut(c, Nonce x, _) -> 
      if Map.mem goal.target (Var.str x) then 
        let w = Map.find_exn goal.target (Var.str x) in 
        let target = 
          Map.set (Map.remove goal.target (Var.str x)) ~key:(Var.str x) ~data:w
        in
        check ctx c {goal with target}
      else
        check ctx c goal    
    | MapOut(c, SetTo (x, e), _) ->
      if Map.mem goal.target (Var.str x) then 
        let w = Map.find_exn goal.target (Var.str x) in 
        let target = 
          union (map_of_varset (Expr.vars e))
                (Map.set (Map.remove goal.target (Var.str x)) ~key:(Var.str x) ~data:w)
        in
        check ctx c {goal with target}
      else
        check ctx c goal
    | MapOut(c, Del x, _) -> 
      assert (not (Map.mem goal.target (Var.str x)));
      check ctx c goal
    | MapOut(c, Rename _, _) | MapOut(c, Add _, _) ->
      check ctx c goal
    | MapIn(c, Project xs, _) -> 
      let xsset = String.Set.of_list (List.map ~f:Var.str xs) in 
      let matchset = Map.key_set goal.source in 
      assert (Set.is_subset matchset ~of_:xsset);
      check ctx c goal
    | MapIn(c, Del x, _) | MapIn(c, WildCard x, _ ) ->
      (* assert (not (Map.mem goal.source (Var.str x))); *)
      assert (not (Set.exists (BExpr.free_vars goal.refine) ~f:(Var.equal x)));
      let goal' = 
        {goal with
         (* TODO: *)
         (* refine = BExpr.subst x TTrue goal.refine; *)
         source = Map.remove goal.source (Var.str x)}
      in
      check ctx c goal'
    | MapIn(c, SetTo(x,e), _) -> 
      let refine = BExpr.subst x e goal.refine in
      let goal' =
        {goal with
         source = match e with
         | Var x' ->
           Map.remove
             (Map.set goal.source
                      ~key:(Var.str x')
                      ~data:(Map.find_exn goal.source (Var.str x)))
             (Var.str x)
         | _ -> failwith "unimplemented"}
      in
      check ctx c {goal' with refine}
    | MapIn(c, CubeFilter cube,_ ) ->
      let phi = Semantics.Match.map_to_bexpr cube in 
      check ctx c {goal with refine = BExpr.and_ phi goal.refine}
    | MapIn(c, Filter phi, _) -> 
      (* This is overly strong, but idk how to fix it*)
      check ctx c {goal with refine = BExpr.and_ phi goal.refine}
end
