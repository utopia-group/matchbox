open Core
open Stijl
open Semantics

(* Standalone test for the Z3-backed [Verifier].

   NB: this is a *separate* test executable from [stijl_test], whose committed
   modules currently do not compile against the present [lib/] (they reference
   removed names like [BaseLogic.ProvRow] / [Action] / the [Table] constructor).
   Keeping the verifier test standalone lets it build and run independently. *)

let drop = MagmaAction.make "drop"
let allow = MagmaAction.make "allow"

(* A single-key ACL: dport==22 -> drop, anything else -> allow. *)
let acl_type : Type.t =
  {
    is_private = false;
    hw = TCAM;
    keys = String.Map.singleton "dport" 16;
    actions = Type.ActionSet.of_list [drop; allow];
    data = String.Map.empty;
  }

let exact16 v = Match.exact (Bit.Vector.of_int ~width:16 v)
let wild16 = Match.Ternary (Trit.Vector.wc 16)

let acl_table : MatchActionTable.t =
  [
    MatchAction.make TCAM (String.Map.singleton "dport" (exact16 22)) drop Data.empty;
    MatchAction.make TCAM (String.Map.singleton "dport" wild16) allow Data.empty;
  ]

(* dport == [v] (width 16) as a precondition formula. *)
let dport_eq v =
  let open Gpl in
  BExpr.(Expr.var (Var.make "dport" 16) == Expr.bvi v 16)

let action_is a = [ Property.ActionEq a ]

let is_valid = function Verifier.Valid -> true | _ -> false
let is_cex = function Verifier.Counterexample _ -> true | _ -> false

(* { dport == 22 } => { $action == drop }  holds. *)
let test_action_holds () =
  let p = Property.{ table = "acl"; pre = dport_eq 22; post = action_is drop } in
  Alcotest.(check bool) "matched packet drops" true
    (is_valid (Verifier.check acl_type acl_table p))

(* { dport == 80 } => { $action == drop }  fails (it is allowed), with a cex. *)
let test_action_fails () =
  let p = Property.{ table = "acl"; pre = dport_eq 80; post = action_is drop } in
  let result = Verifier.check acl_type acl_table p in
  Alcotest.(check bool) "unmatched packet is a counterexample" true (is_cex result);
  match result with
  | Verifier.Counterexample binds ->
    Alcotest.(check bool) "counterexample reports dport" true
      (List.Assoc.mem binds "dport" ~equal:String.equal)
  | _ -> ()

(* A vacuous precondition (dport == 22 && dport == 80) makes anything valid. *)
let test_vacuous_pre () =
  let pre = Gpl.BExpr.and_ (dport_eq 22) (dport_eq 80) in
  let p = Property.{ table = "acl"; pre; post = action_is drop } in
  Alcotest.(check bool) "unsatisfiable precondition is vacuously valid" true
    (is_valid (Verifier.check acl_type acl_table p))

(* An action the table can never emit is never guaranteed. *)
let test_unreachable_action () =
  let p = Property.{ table = "acl"; pre = dport_eq 22; post = action_is (MagmaAction.make "punt") } in
  Alcotest.(check bool) "guaranteeing an unreachable action fails" true
    (is_cex (Verifier.check acl_type acl_table p))

let () =
  Alcotest.run "verifier"
    [
      ( "hoare",
        [
          Alcotest.test_case "action guarantee holds" `Quick test_action_holds;
          Alcotest.test_case "action guarantee fails with cex" `Quick test_action_fails;
          Alcotest.test_case "vacuous precondition" `Quick test_vacuous_pre;
          Alcotest.test_case "unreachable action" `Quick test_unreachable_action;
        ] );
    ]
