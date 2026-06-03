open Core
open Semantics

(* Z3-backed verifier for matchbox programs: decides whether an (evaluated)
   match-action table [tbl] of type [typ] satisfies a Hoare-style property [p].

   We encode the table's first-match-wins input->output relation in SMT, assert
   the precondition and the *negation* of the postcondition, and ask Z3 for a
   model.  UNSAT  => the table satisfies the property (Valid).
   SAT    => the model is a concrete counterexample packet (Counterexample).

   The action universe and key/data widths are taken from the table *type* (not
   the evaluated rows) so that [$action] has a stable encoding even when the
   table is empty or never emits some declared action.  A packet that matches no
   row leaves [$action] unconstrained ("miss"); if such a packet is admitted by
   the precondition it surfaces as a counterexample, which is sound. *)

type result =
  | Valid
  | Counterexample of (string * string) list   (* variable -> bitvector value *)

let z3 () = Runner.init "z3 -smt2 -in"

(* Stable list of the actions this table may emit, with their bitvector ids.
   Mirrors MinimalTCAM's convention that the action bitvector width equals the
   number of actions (ids 0..n-1). *)
let action_universe (typ : Type.t) : MagmaAction.t list =
  Type.get_actions typ |> Set.to_list

let action_width acts = List.length acts

let act_id acts a =
  List.findi acts ~f:(fun _ a' -> MagmaAction.equal a a')
  |> Option.map ~f:fst

(* Priority-ordered ("first match wins") fold shared by the action and data
   encodings: applies [emit reaching match_cond row] to accumulate a constraint
   for each row, threading the "not yet matched by a higher-priority row" guard. *)
let priority_fold (tbl : MatchActionTable.t) ~emit : SMT.expr =
  let open SMT in
  let rows, _ =
    List.fold tbl ~init:([], true_)
      ~f:(fun (encoded, reaching) (row : MatchAction.t) ->
        let _, match_cond = MinimalTCAM.match_to_smt row.matches in
        let encoded = encoded @ emit reaching match_cond row in
        (encoded, and_ [reaching; not match_cond]))
  in
  and_ rows

(* keys -> $action *)
let action_semantics acts (tbl : MatchActionTable.t) : SMT.expr =
  let open SMT in
  let anum = action_width acts in
  priority_fold tbl ~emit:(fun reaching match_cond row ->
    match act_id acts row.action with
    | None -> []   (* row emits an action outside the declared type; skip *)
    | Some aid ->
      let action_cond = (=) [var MinimalTCAM.action_var; bv aid anum] in
      [ implies [and_ [reaching; match_cond]; action_cond] ])

(* keys -> output data field [field] *)
let data_semantics (tbl : MatchActionTable.t) (field : string) : SMT.expr =
  let open SMT in
  priority_fold tbl ~emit:(fun reaching match_cond row ->
    match Data.find row.data field with
    | None -> []
    | Some v -> [ implies [and_ [reaching; match_cond]; (=) [var field; bv' v]] ])

let guarantee_to_smt acts (g : Property.guarantee) : SMT.expr =
  let open SMT in
  match g with
  | Property.ActionEq a ->
    (match act_id acts a with
     | Some aid -> (=) [var MinimalTCAM.action_var; bv aid (action_width acts)]
     | None -> false_)   (* this table can never emit [a], so the guarantee fails *)
  | Property.Pred phi -> SMT.of_bexpr phi

let post_to_smt acts (post : Property.guarantee list) : SMT.expr =
  SMT.and_ (List.map post ~f:(guarantee_to_smt acts))

(* Output data fields actually mentioned by the postcondition's predicates,
   restricted to fields that exist in the table's data schema. *)
let referenced_data_fields (typ : Type.t) (post : Property.guarantee list) : string list =
  let data_names = Type.get_data typ |> Map.key_set in
  List.concat_map post ~f:(function
    | Property.ActionEq _ -> []
    | Property.Pred phi ->
      Gpl.BExpr.free_vars phi |> Set.to_list |> List.map ~f:Gpl.Var.str)
  |> List.filter ~f:(Set.mem data_names)
  |> List.dedup_and_sort ~compare:String.compare

let check (typ : Type.t) (tbl : MatchActionTable.t) (p : Property.t) : result =
  let open SMT in
  let acts = action_universe typ in
  let anum = action_width acts in
  let keys = Type.get_keys typ in
  let data_widths = Type.get_data typ in
  let data_fields = referenced_data_fields typ p.post in
  let declarations =
    List.map keys ~f:(fun (x, w) -> declare_const x (bv_sort w))
    @ [ declare_const MinimalTCAM.action_var (bv_sort anum) ]
    @ List.map data_fields ~f:(fun d ->
        declare_const d (bv_sort (Map.find_exn data_widths d)))
  in
  let semantics = action_semantics acts tbl :: List.map data_fields ~f:(data_semantics tbl) in
  let queried = List.map keys ~f:fst @ [MinimalTCAM.action_var] @ data_fields in
  let smt =
    declarations
    @ [ assert_ (and_ semantics);
        assert_ (of_bexpr p.pre);
        assert_ (not (post_to_smt acts p.post));
        check_sat;
        get_value queried ]
  in
  match SMT.check (SMT.run (z3 ()) smt) with
  | None -> Valid
  | Some model ->
    Counterexample
      (List.filter_map queried ~f:(fun v ->
         Option.map (SMT.Model.find model v) ~f:(fun value -> (v, value))))
