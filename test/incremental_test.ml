open Core
open Stijl
open Semantics
open BaseLogic

(* Differential tests for [Incremental]: after bootstrap and after *every*
   update batch, every step's incrementally-maintained table must equal --
   same rows, same first-match-wins order -- the table produced by a full
   from-scratch [BaseInterpreter.eval_program] on the current base config.

   NB: like [verifier_test], this is a *separate* test executable from
   [stijl_test], whose committed modules do not compile against the present
   [lib/]. *)

(* ------------------------------------------------------------------ *)
(* Row/program builders                                                *)
(* ------------------------------------------------------------------ *)

let bv v = Bit.Vector.of_int v ~width:8
let ex v = Match.exact (bv v)
let wc = Match.Ternary (Trit.Vector.wc 8)

let row keys action data =
  MatchAction.make TCAM
    (String.Map.of_alist_exn keys)
    (MagmaAction.make action)
    (String.Map.of_alist_exn data)

let var x = Var.make x 8

let sym name = Symbol.make name [] 0
let def name definition = {defined = sym name; definition}

(* ------------------------------------------------------------------ *)
(* Differential harness                                                *)
(* ------------------------------------------------------------------ *)

(* The central property: incremental == non-incremental, for every step,
   checked against [BaseInterpreter.eval_program] on the accumulated base
   tables. *)
let check_state ~label st prog =
  let results, _ =
    BaseInterpreter.eval_program (Incremental.base_config st) prog
  in
  List.iteri results ~f:(fun i (name, expected) ->
    let actual = Incremental.step_table_exn st i in
    let ok = MatchActionTable.equal expected actual in
    if not ok then
      Printf.printf
        "%s: step %d (%s) diverged\n--- full recompute:\n%s\n--- incremental:\n%s\n"
        label i name
        (MatchActionTable.to_string expected)
        (MatchActionTable.to_string actual);
    Alcotest.(check bool)
      (sprintf "%s: step %d (%s) == full recompute" label i name)
      true ok)

(* Bootstrap, then apply each batch, re-checking the differential property
   every time. Returns the per-batch step deltas for extra assertions. *)
let run_scenario prog init_rows batches =
  let st = Incremental.bootstrap prog init_rows in
  check_state ~label:"bootstrap" st prog;
  let _, rev_deltas =
    List.foldi batches ~init:(st, []) ~f:(fun i (st, acc) batch ->
      let st, deltas = Incremental.apply_batch ~strict:true st prog batch in
      check_state ~label:(sprintf "batch %d" i) st prog;
      (st, deltas :: acc))
  in
  List.rev rev_deltas

let ins table ?(priority = 100) r = Incremental.Insert {table; row = r; priority}

let del table ?(priority = 100) keys =
  Incremental.Delete
    {table; matches = String.Map.of_alist_exn keys; priority}

let delta_of deltas name =
  List.Assoc.find_exn deltas name ~equal:String.equal

(* ------------------------------------------------------------------ *)
(* Base tables shared by several scenarios                             *)
(*   f : keys {k}  data {n}    (rule lookup feeding Compose)           *)
(*   g : keys {n}  data {p}    (with a low-priority catch-all)         *)
(*   a, b : keys {k} data {da}/{db}                                    *)
(* ------------------------------------------------------------------ *)

let f_rows =
  [ ("f", row [("k", ex 1)] "fwd" [("n", bv 1)], 100);
    ("f", row [("k", ex 2)] "fwd" [("n", bv 2)], 100) ]

let g_rows =
  [ ("g", row [("n", ex 1)] "setp" [("p", bv 10)], 100);
    ("g", row [("n", ex 2)] "setp" [("p", bv 20)], 100);
    ("g", row [("n", wc)] "miss" [("p", bv 0)], 1000) ]

(* ------------------------------------------------------------------ *)
(* Scenarios                                                           *)
(* ------------------------------------------------------------------ *)

(* MapOut (Rename, Project, Del, SetTo) and MapIn (WildCard, Del, Project,
   SetTo, CubeFilter) over a single base table, with inserts and deletes. *)
let test_map_ops () =
  let t = Clause.id (sym "t") in
  let prog =
    [ def "ren" Clause.(t |>> OutTfx.Rename (MagmaAction.make "fwd", MagmaAction.make "go"));
      def "prj" Clause.(t |>> OutTfx.Project [var "d"]);
      def "dl" Clause.(t |>> OutTfx.Del (var "e"));
      def "st" Clause.(t |>> OutTfx.SetTo (var "e", Gpl.Expr.Var (var "d")));
      def "wild" Clause.(MatchTfx.WildCard (var "k") <<| t);
      def "delk" Clause.(MatchTfx.Del (var "j") <<| t);
      def "prjk" Clause.(MatchTfx.Project [var "k"] <<| t);
      def "stk" Clause.(MatchTfx.SetTo (var "j", Gpl.Expr.Var (var "k")) <<| t);
      def "cube"
        Clause.(MatchTfx.CubeFilter (String.Map.singleton "k" (ex 5)) <<| t);
    ]
  in
  let mk_row k j d = row [("k", ex k); ("j", ex j)] "fwd" [("d", bv d); ("e", bv 0)] in
  let init = [("t", mk_row 1 1 11, 100); ("t", mk_row 5 2 55, 100)] in
  let batches =
    [ [ins "t" (mk_row 3 3 33)];                          (* plain insert *)
      [del "t" [("k", ex 1); ("j", ex 1)]];               (* delete (drops a cube row too) *)
      [ins "t" (mk_row 5 7 77) ~priority:50];             (* second k=5 row, higher prio *)
      [del "t" [("k", ex 5); ("j", ex 2)]; ins "t" (mk_row 2 2 22)] ]
  in
  ignore (run_scenario prog init batches)

(* Override: a change on one side must not disturb the other side's rows;
   both-side updates in one batch must interleave correctly (f-side first). *)
let test_override () =
  let prog = [def "o" Clause.(id (sym "a") |> id (sym "b"))] in
  let arow k = row [("k", ex k)] "fwd" [("da", bv k)] in
  let brow k = row [("k", ex k)] "fwd" [("da", bv (k + 100))] in
  let init = [("a", arow 1, 100); ("b", brow 2, 100)] in
  let deltas =
    run_scenario prog init
      [ [ins "a" (arow 3)];
        [ins "b" (brow 4)];
        [ins "a" (arow 5); ins "b" (brow 6); del "a" [("k", ex 1)]] ]
  in
  (* the b-only batch must not touch any a-side (left) rank *)
  let d = delta_of (List.nth_exn deltas 1) "o" in
  List.iter (d.ins @ d.del) ~f:(fun (r, _) ->
    match (r : Rank.t) with
    | Side (1, _) -> ()
    | r ->
      Alcotest.failf "b-only update produced a non-right-side rank %s"
        (Rank.to_string r))

(* Join: bilinear delta rule, including pairs dropped by empty match
   intersection, under f-only, g-only, and both-sides updates. *)
let test_join () =
  let prog = [def "j" Clause.(id (sym "a") * id (sym "b"))] in
  let arow k v = row [("k", ex k)] "left" [("da", bv v)] in
  let brow k y v = row [("k", ex k); ("y", ex y)] "right" [("db", bv v)] in
  let init =
    [ ("a", arow 1 10, 100); ("a", arow 2 20, 100);
      ("b", brow 1 7 70, 100); ("b", brow 9 8 80, 100) ]
  in
  ignore
    (run_scenario prog init
       [ [ins "a" (arow 9 90)];                       (* pairs with b's k=9 row *)
         [ins "b" (brow 2 5 50)];                     (* pairs with a's k=2 row *)
         [del "a" [("k", ex 1)]];                     (* kills all k=1 pairs *)
         [ins "a" (arow 3 30); ins "b" (brow 3 1 11)] (* Δf x Δg corner *);
         [del "b" [("k", ex 9); ("y", ex 8)]; ins "a" (arow 9 91) ~priority:50] ])

(* Compose: the heart of the incremental scheme. Covers shadowing inserts,
   un-shadowing deletes, no-op g changes (candidate-set soundness), f-side
   changes, and simultaneous f+g changes. *)
let test_compose () =
  let prog = [def "c" Clause.(id (sym "f") >>> id (sym "g"))] in
  let frow k n = row [("k", ex k)] "fwd" [("n", bv n)] in
  let grow_exact n p prio = ("g", row [("n", ex n)] "setp" [("p", bv p)], prio) in
  ignore grow_exact;
  let deltas =
    run_scenario prog (f_rows @ g_rows)
      [ (* shadow: a higher-priority g row changes the lookup for n=2 *)
        [ins "g" (row [("n", ex 2)] "setp" [("p", bv 99)]) ~priority:50];
        (* un-shadow: deleting it must restore the old result *)
        [del "g" [("n", ex 2)] ~priority:50];
        (* a g change matching no f key must produce an empty delta *)
        [ins "g" (row [("n", ex 77)] "setp" [("p", bv 7)]) ~priority:50];
        (* f-side insert (hits the catch-all) and delete *)
        [ins "f" (frow 3 5)];
        [del "f" [("k", ex 1)]];
        (* both sides at once *)
        [ ins "f" (frow 4 2);
          ins "g" (row [("n", ex 5)] "setp" [("p", bv 55)]) ~priority:50 ] ]
  in
  let no_match = delta_of (List.nth_exn deltas 2) "c" in
  Alcotest.(check bool)
    "g change matching no f key yields an empty compose delta" true
    (Incremental.Delta.is_empty no_match)

(* A table literal under Override: the literal side never changes. *)
let test_table_literal () =
  let lit =
    Clause.table "lit" [row [("k", ex 0)] "fwd" [("da", bv 0)]]
  in
  let prog = [def "o" Clause.(lit |> id (sym "a"))] in
  let arow k = row [("k", ex k)] "fwd" [("da", bv k)] in
  ignore
    (run_scenario prog
       [("a", arow 1, 100)]
       [[ins "a" (arow 2)]; [del "a" [("k", ex 1)]]])

(* A step that redefines a base symbol of the same name (eval_program allows
   shadowing): updates to the base version must flow through both the
   redefining step and later readers of the redefined name. *)
let test_shadowing () =
  let prog =
    [ def "e" Clause.(id (sym "e") |>> OutTfx.Rename (MagmaAction.make "fwd", MagmaAction.make "go"));
      def "z" Clause.(MatchTfx.WildCard (var "k") <<| id (sym "e")) ]
  in
  let erow k = row [("k", ex k)] "fwd" [("da", bv k)] in
  ignore
    (run_scenario prog
       [("e", erow 1, 100)]
       [[ins "e" (erow 2)]; [del "e" [("k", ex 1)]]])

(* Update independence: a change to one base table must leave a derived
   table over a different base table with an empty delta (short-circuit). *)
let test_independence () =
  let prog =
    [ def "x" Clause.(id (sym "a") |>> OutTfx.Rename (MagmaAction.make "fwd", MagmaAction.make "go"));
      def "y" Clause.(id (sym "b") |>> OutTfx.Rename (MagmaAction.make "fwd", MagmaAction.make "go")) ]
  in
  let arow k = row [("k", ex k)] "fwd" [("da", bv k)] in
  let deltas =
    run_scenario prog
      [("a", arow 1, 100); ("b", arow 2, 100)]
      [[ins "a" (arow 3)]]
  in
  let d = delta_of (List.nth_exn deltas 0) "y" in
  Alcotest.(check bool) "unrelated table has an empty delta" true
    (Incremental.Delta.is_empty d)

(* Insert + delete of the same row within one atomic batch must cancel. *)
let test_cancel_within_batch () =
  let prog = [def "x" Clause.(id (sym "a") |>> OutTfx.Rename (MagmaAction.make "fwd", MagmaAction.make "go"))] in
  let arow k = row [("k", ex k)] "fwd" [("da", bv k)] in
  let deltas =
    run_scenario prog
      [("a", arow 1, 100)]
      [[ins "a" (arow 9) ~priority:70; del "a" [("k", ex 9)] ~priority:70]]
  in
  let d = delta_of (List.nth_exn deltas 0) "x" in
  Alcotest.(check bool) "insert+delete in one batch cancels" true
    (Incremental.Delta.is_empty d)

(* Delete then re-insert the same content across batches. *)
let test_delete_reinsert () =
  let prog = [def "c" Clause.(id (sym "f") >>> id (sym "g"))] in
  let frow k n = row [("k", ex k)] "fwd" [("n", bv n)] in
  ignore
    (run_scenario prog (f_rows @ g_rows)
       [[del "f" [("k", ex 2)]]; [ins "f" (frow 2 2)]])

(* NB on [MatchTfx.Filter] (the only 1->many MapIn transform): both the full
   interpreter and the incremental evaluator reach it through the same
   [BaseInterpreter.apply_in_tfx] call, but its z3 backend
   ([GuardSynthesis.split]) currently deadlocks against the installed z3
   (verified standalone, independent of this feature; no committed .mb
   program uses [filter]). Until that is fixed, the 1->many splitting cannot
   be differentially tested end-to-end; the [Sub]-rank range-delete logic it
   relies on is exercised by the 1->1 (every other MapIn tfx) and 1->0
   (CubeFilter drop) cases above. *)

(* Randomized soak: a Compose-over-Override pipeline under a fixed-seed
   random stream of inserts and deletes, differentially checked after every
   batch. *)
let test_randomized () =
  let prog =
    [ def "u" Clause.(id (sym "a") |> id (sym "b"));
      def "c" Clause.(id (sym "u") >>> id (sym "g")) ]
  in
  let mk_row k n = row [("k", ex k)] "fwd" [("n", bv n)] in
  let init =
    [ ("a", mk_row 0 0, 100);
      ("b", mk_row 1 1, 100);
      ("g", row [("n", wc)] "miss" [("p", bv 0)], 1000) ]
  in
  Random.init 42;
  (* live rows we may delete, per table: (matches, priority) *)
  let live = ref String.Map.empty in
  let remember table keys prio =
    live := Map.add_multi !live ~key:table ~data:(keys, prio)
  in
  remember "a" [("k", ex 0)] 100;
  remember "b" [("k", ex 1)] 100;
  let random_op () =
    let table = List.nth_exn ["a"; "b"; "g"] (Random.int 3) in
    let deletable = Map.find !live table |> Option.value ~default:[] in
    if (not (List.is_empty deletable)) && Random.int 4 = 0 then begin
      let i = Random.int (List.length deletable) in
      let keys, priority = List.nth_exn deletable i in
      live := Map.set !live ~key:table ~data:(List.filteri deletable ~f:(fun j _ -> j <> i));
      del table keys ~priority
    end
    else
      let priority = List.nth_exn [50; 100; 150] (Random.int 3) in
      if String.(table = "g") then begin
        let n = Random.int 4 in
        let keys = [("n", ex n)] in
        remember table keys priority;
        ins table (row keys "setp" [("p", bv (Random.int 100))]) ~priority
      end
      else begin
        let k = Random.int 8 in
        let keys = [("k", ex k)] in
        remember table keys priority;
        ins table (mk_row k (Random.int 4)) ~priority
      end
  in
  (* generate with explicit recursion: [List.init] applies [f] in an
     unspecified order, which would scramble the stateful generator (a delete
     could end up batched before the insert it refers to) *)
  let rec gen_ops k acc =
    if Int.(k = 0) then List.rev acc else gen_ops (k - 1) (random_op () :: acc)
  in
  let rec gen_batches k acc =
    if Int.(k = 0) then List.rev acc
    else gen_batches (k - 1) (gen_ops (1 + Random.int 3) [] :: acc)
  in
  ignore (run_scenario prog init (gen_batches 12 []))

let () =
  Alcotest.run "incremental"
    [
      ( "differential",
        [
          Alcotest.test_case "map in/out transforms" `Quick test_map_ops;
          Alcotest.test_case "override" `Quick test_override;
          Alcotest.test_case "join" `Quick test_join;
          Alcotest.test_case "compose shadow/unshadow" `Quick test_compose;
          Alcotest.test_case "table literal" `Quick test_table_literal;
          Alcotest.test_case "base symbol shadowing" `Quick test_shadowing;
          Alcotest.test_case "independent tables short-circuit" `Quick test_independence;
          Alcotest.test_case "cancel within batch" `Quick test_cancel_within_batch;
          Alcotest.test_case "delete then reinsert" `Quick test_delete_reinsert;
          Alcotest.test_case "randomized soak" `Quick test_randomized;
        ] );
    ]
