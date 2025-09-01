open Core
open Gpl
open BaseLogic
module DepFunDep = struct 
  type t = {
    refine : BExpr.t;
    source : String.Set.t;
    target : String.Set.t;
  }

  let fd_eq fd1 fd2 = 
    BExpr.equal fd1.refine fd2.refine
    && Set.equal fd1.source fd2.source
    && Set.equal fd1.target fd2.target

  type itfc_spec = t String.Map.t 

  let inherent_fd (gamma : Type.ctx) (f : Symbol.t) : t =
    let table_type = Type.find_table_exn gamma (Symbol.to_string f) in 
    let data_types = Type.get_data table_type in 
    let key_types = Type.get_keys table_type in 
    { refine = BExpr.true_;
      source = Set.of_list (module String) (List.map ~f:fst key_types);
      target = Set.of_map_keys data_types;
    }

  let find_fd (spec : itfc_spec) (symbol : Symbol.t) = 
    Map.find spec (Symbol.to_string symbol)

  let implies (spec : itfc_spec) (symbol : Symbol.t) (fd : t) = 
    Option.filter (find_fd spec symbol) ~f:(fd_eq fd)

  let check (ctx : itfc_spec) (gamma : Type.ctx) (clause : Clause.t) : t option =
    let (let*) b f = Option.bind b ~f in 
    let (let+) b f = Option.map b ~f in
    match clause with 
    | Id f -> 
      find_fd ctx f
    | Join (f, g, _) -> 
      let* f_fd = find_fd ctx f in
      let+ g_fd = find_fd ctx g in
      assert (Set.are_disjoint g_fd.target f_fd.target);
      { refine = BExpr.and_ f_fd.refine g_fd.refine;
        source = Set.union f_fd.source g_fd.source;
        target = Set.union g_fd.target g_fd.target;
      }
    | Compose (f, g) -> 
      let* f_fd = find_fd ctx f in 
      let+ g_fd = find_fd ctx g in
      assert (Set.equal f_fd.target g_fd.source);
      assert (BExpr.(equal true_) f_fd.refine);
      assert (BExpr.(equal true_) g_fd.refine);
      {  refine = BExpr.true_;
         source = f_fd.source;
         target = g_fd.target
      }
    | Invert f -> 
      let f_fd = inherent_fd gamma f in 
      let f_inv_fd = { f_fd with 
        source = f_fd.target;
        target = f_fd.source
      } in 
      implies ctx f f_inv_fd
    | MapOut(f, tfx) ->
      let* f_fd = find_fd ctx f in 
      begin match tfx with 
        | Project xs -> 
          let xs_set = String.Set.of_list xs in 
          Some {
            f_fd with 
              target = Set.(inter xs_set f_fd.target)
          }
        | SetTo (d, e) -> 
          (* e must denote a function *)
          let es = ActionTfx.e_fvs e in
          let fvs_determined = {f_fd with target = es} in 
          let+ _ = implies ctx f fvs_determined in 
          {f_fd with target = Set.add f_fd.target d }
        | Filter _ ->  failwith "not sure how to filter outputs"
      end 
    | MapIn(f, tfx) -> 
      let* f_fd = find_fd ctx f in 
      match tfx with 
      | Project keys ->
        (* It must be the case that f : keys -> f_fd.target *)
        let new_fd = {f_fd with source = String.Set.of_list keys} in
        implies ctx f new_fd
      | SetTo (k, e) -> 
        (* e has to be invertible! *)
        let es = MatchTfx.e_fvs e in 
        assert (Set.(equal (union es (remove f_fd.source k)) f_fd.source));
        Some {f_fd with 
          source = Set.add f_fd.source k;
        }
      | Filter matches ->
        let filtered_fd = 
          {
            f_fd with 
              refine = Semantics.Match.map_to_bexpr matches;
          }
        in
        let+ _ = implies ctx f filtered_fd in
        f_fd
end

