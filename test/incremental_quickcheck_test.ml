open Core
open Stijl
open Semantics
open BaseLogic

(* Property-based equivalence test (Jane Street Core.Quickcheck):
   for randomly generated programs, initial configs, and update sequences,
   the incremental evaluator ([Incremental]) must produce exactly the same
   tables -- same rows, same first-match-wins order -- as the monolithic
   interpreter ([BaseInterpreter.eval_program]), after bootstrap and after
   every update batch.

   Cases are generated as a small first-order DSL (sexp-able, so a failing
   case prints reproducibly) and *interpreted* into [Clause.t] programs. The
   interpretation tracks which data fields are guaranteed present on every
   row so that generated programs are valid by construction: random raw
   clauses would crash both modes identically (Compose into a table that
   misses some lookup key, Join with colliding data fields, SetTo over an
   absent field), which would test nothing.

   Fixed universe: 4-bit fields throughout.
     a, b : keys {k, j}  data {n}  action fwd     (updatable)
     g    : keys {n}     data {p}  actions setp   (updatable; plus an
            undeletable wildcard catch-all so Compose stays total)
   Programs are 1-3 steps; each step may reference a, b, or any earlier
   step, and may shadow the base name "a" (eval_program allows this).
   Excluded by design: MapIn Filter (its z3 backend deadlocks -- see
   incremental_test.ml) and Nonce (documented incremental/full divergence). *)

(* ------------------------------------------------------------------ *)
(* Case DSL                                                            *)
(* ------------------------------------------------------------------ *)

type mtch = MExact of int | MWild | MMask of int * int [@@deriving sexp]

type rowd = {kf : mtch; jf : mtch; nv : int; prio : int} [@@deriving sexp]
type growd = {nf : mtch; pv : int; gprio : int} [@@deriving sexp]

type src = SrcA | SrcB | SrcPrev of int [@@deriving sexp]

type kop = KDelJ | KWildK | KProjK | KSetJK | KCube of int [@@deriving sexp]
type dop = DRen | DCopy | DDel [@@deriving sexp]

type shape =
  | Chain of src * kop list * dop list   (* MapIn/MapOut chain over one source *)
  | Both of src * src * kop list         (* Override of two sources, then MapIns *)
  | Comp of src * kop list               (* (MapIn chain over source) >>> g *)
  | Joined of src * src                  (* Join, sides renamed apart *)
[@@deriving sexp]

type step_desc = {shadow : bool; shape : shape} [@@deriving sexp]

type tbl = TA | TB | TG [@@deriving sexp]

type upd =
  | UIns of bool * rowd                  (* true -> a, false -> b *)
  | UInsG of growd
  | UDel of tbl * int                    (* delete the (i mod live)-th live row *)
[@@deriving sexp]

type case = {
  prog : step_desc list;
  a0 : rowd list;
  b0 : rowd list;
  g0 : growd list;
  batches : upd list list;
}
[@@deriving sexp]

(* ------------------------------------------------------------------ *)
(* Interpretation                                                      *)
(* ------------------------------------------------------------------ *)

let bv4 v = Bit.Vector.of_int (v land 15) ~width:4
let v4 x = Var.make x 4
let sym name = Symbol.make name [] 0

let interp_mtch = function
  | MExact v -> Match.exact (bv4 v)
  | MWild -> Match.Ternary (Trit.Vector.wc 4)
  | MMask (v, m) -> Match.Ternary (Trit.Vector.of_bitmask (bv4 v) (bv4 m))

let interp_rowd {kf; jf; nv; prio} =
  ( MatchAction.make TCAM
      (String.Map.of_alist_exn [("k", interp_mtch kf); ("j", interp_mtch jf)])
      (MagmaAction.make "fwd")
      (String.Map.singleton "n" (bv4 nv)),
    prio )

let interp_growd {nf; pv; gprio} =
  ( MatchAction.make TCAM
      (String.Map.singleton "n" (interp_mtch nf))
      (MagmaAction.make "setp")
      (String.Map.singleton "p" (bv4 pv)),
    gprio )

(* Never inserted into the deletable pool: keeps g total for Compose. *)
let g_catchall =
  ( MatchAction.make TCAM
      (String.Map.singleton "n" (Match.Ternary (Trit.Vector.wc 4)))
      (MagmaAction.make "miss")
      (String.Map.singleton "p" (bv4 0)),
    1000 )

let interp_kop c = function
  | KDelJ -> Clause.(MatchTfx.Del (v4 "j") <<| c)
  | KWildK -> Clause.(MatchTfx.WildCard (v4 "k") <<| c)
  | KProjK -> Clause.(MatchTfx.Project [v4 "k"] <<| c)
  | KSetJK -> Clause.(MatchTfx.SetTo (v4 "j", Gpl.Expr.Var (v4 "k")) <<| c)
  | KCube v ->
    Clause.(MatchTfx.CubeFilter (String.Map.singleton "k" (Match.exact (bv4 v))) <<| c)

(* [avail] = data fields guaranteed present on every row of the table. *)
let interp_dop (c, avail) = function
  | DRen ->
    ( Clause.(c |>> OutTfx.Rename (MagmaAction.make "fwd", MagmaAction.make "go")),
      avail )
  | DCopy -> (
    match Set.min_elt avail with
    | Some f ->
      ( Clause.(c |>> OutTfx.SetTo (v4 "m", Gpl.Expr.Var (v4 f))),
        Set.add avail "m" )
    | None -> (c, avail))
  | DDel -> (
    match Set.min_elt avail with
    | Some f -> (Clause.(c |>> OutTfx.Del (v4 f)), Set.remove avail f)
    | None -> (c, avail))

(* Every data field any generated table can carry. Join sides delete the
   whole universe except their own renamed field, so [Data.disjoint_union]
   can never collide -- even when joining a table with itself or with the
   output of an earlier Join. *)
let data_universe = ["m"; "n"; "na"; "nb"; "p"]

let join_side name avail uniq =
  let c = Clause.id (sym name) in
  let c =
    match Set.min_elt avail with
    | Some f -> Clause.(c |>> OutTfx.SetTo (v4 uniq, Gpl.Expr.Var (v4 f)))
    | None -> c
  in
  let c =
    List.fold data_universe ~init:c ~f:(fun c f ->
      if String.(f = uniq) then c else Clause.(c |>> OutTfx.Del (v4 f)))
  in
  (c, if Set.is_empty avail then String.Set.empty else String.Set.singleton uniq)

let interp_shape avails defs shape : Clause.t * String.Set.t =
  let avail_of n = Map.find avails n |> Option.value ~default:String.Set.empty in
  let src_name = function
    | SrcA -> "a"
    | SrcB -> "b"
    | SrcPrev i -> (
      match defs with
      | [] -> "a"
      | l -> List.nth_exn l (i mod List.length l))
  in
  match shape with
  | Chain (s, kops, dops) ->
    let name = src_name s in
    let c = List.fold kops ~init:(Clause.id (sym name)) ~f:interp_kop in
    List.fold dops ~init:(c, avail_of name) ~f:interp_dop
  | Both (s1, s2, kops) ->
    let n1 = src_name s1 and n2 = src_name s2 in
    let c = Clause.override (Clause.id (sym n1)) (Clause.id (sym n2)) in
    let c = List.fold kops ~init:c ~f:interp_kop in
    (* conservative: only fields on *every* row of both sides *)
    (c, Set.inter (avail_of n1) (avail_of n2))
  | Comp (s, kops) -> (
    (* Compose looks the source's data up in g, so the source must be
       guaranteed to carry the lookup key [n] on every row; fall back to the
       current "a", or degrade to a plain chain if nothing n-bearing exists. *)
    let name = src_name s in
    let name = if Set.mem (avail_of name) "n" then name else "a" in
    let c = List.fold kops ~init:(Clause.id (sym name)) ~f:interp_kop in
    if Set.mem (avail_of name) "n" then
      (Clause.(c >>> id (sym "g")), String.Set.singleton "p")
    else (c, avail_of name))
  | Joined (s1, s2) ->
    let n1 = src_name s1 and n2 = src_name s2 in
    let c1, a1 = join_side n1 (avail_of n1) "na" in
    let c2, a2 = join_side n2 (avail_of n2) "nb" in
    (Clause.join c1 c2, Set.union a1 a2)

let interp_prog (steps : step_desc list) : BaseLogic.t list =
  let avails =
    String.Map.of_alist_exn
      [ ("a", String.Set.singleton "n");
        ("b", String.Set.singleton "n");
        ("g", String.Set.singleton "p") ]
  in
  let _, _, prog =
    List.foldi steps ~init:(avails, [], [])
      ~f:(fun i (avails, defs, prog) {shadow; shape} ->
        let definition, avail = interp_shape avails defs shape in
        let name = if shadow then "a" else sprintf "s%d" i in
        ( Map.set avails ~key:name ~data:avail,
          defs @ [name],
          prog @ [{defined = sym name; definition}] ))
  in
  prog

(* ------------------------------------------------------------------ *)
(* The property                                                        *)
(* ------------------------------------------------------------------ *)

let check ~label st prog =
  let results, _ =
    BaseInterpreter.eval_program (Incremental.base_config st) prog
  in
  List.iteri results ~f:(fun i (name, expected) ->
    let actual = Incremental.step_table_exn st i in
    if not (MatchActionTable.equal expected actual) then
      failwithf
        "%s: step %d (%s) diverged\n--- monolithic:\n%s\n--- incremental:\n%s"
        label i name
        (MatchActionTable.to_string expected)
        (MatchActionTable.to_string actual)
        ())

let tbl_name = function TA -> "a" | TB -> "b" | TG -> "g"

let run_case (c : case) =
  let prog = interp_prog c.prog in
  let tag t f r =
    let row, p = f r in
    (t, row, p)
  in
  let init =
    List.map c.a0 ~f:(tag "a" interp_rowd)
    @ List.map c.b0 ~f:(tag "b" interp_rowd)
    @ List.map c.g0 ~f:(tag "g" interp_growd)
    @ [tag "g" Fn.id g_catchall]
  in
  let st = Incremental.bootstrap prog init in
  check ~label:"bootstrap" st prog;
  (* live rows the generator may delete, per base table (g's catch-all is
     excluded so Compose stays total) *)
  let live_entry f r =
    let row, p = f r in
    (MatchAction.get_matches row, p)
  in
  let live =
    String.Map.of_alist_exn
      [ ("a", List.map c.a0 ~f:(live_entry interp_rowd));
        ("b", List.map c.b0 ~f:(live_entry interp_rowd));
        ("g", List.map c.g0 ~f:(live_entry interp_growd)) ]
  in
  let (_ : Incremental.state * _) =
    List.foldi c.batches ~init:(st, live) ~f:(fun bi (st, live) batch ->
      let live, ops =
        List.fold_map batch ~init:live ~f:(fun live u ->
          match u with
          | UIns (to_a, r) ->
            let table = if to_a then "a" else "b" in
            let row, priority = interp_rowd r in
            ( Map.add_multi live ~key:table
                ~data:(MatchAction.get_matches row, priority),
              Some (Incremental.Insert {table; row; priority}) )
          | UInsG r ->
            let row, priority = interp_growd r in
            ( Map.add_multi live ~key:"g"
                ~data:(MatchAction.get_matches row, priority),
              Some (Incremental.Insert {table = "g"; row; priority}) )
          | UDel (t, i) -> (
            let table = tbl_name t in
            match Map.find live table |> Option.value ~default:[] with
            | [] -> (live, None) (* nothing deletable: drop the op *)
            | rows ->
              let idx = i mod List.length rows in
              let matches, priority = List.nth_exn rows idx in
              ( Map.set live ~key:table
                  ~data:(List.filteri rows ~f:(fun j _ -> j <> idx)),
                Some (Incremental.Delete {table; matches; priority}) )))
      in
      let ops = List.filter_opt ops in
      let st, _ = Incremental.apply_batch ~strict:true st prog ops in
      check ~label:(sprintf "batch %d" bi) st prog;
      (st, live))
  in
  ()

(* ------------------------------------------------------------------ *)
(* Generators                                                          *)
(* ------------------------------------------------------------------ *)

module G = Quickcheck.Generator
open G.Let_syntax

let g_list_between lo hi g =
  let%bind len = Int.gen_incl lo hi in
  G.all (List.init len ~f:(fun _ -> g))

let g_mtch =
  G.weighted_union
    [ (3., G.map (Int.gen_incl 0 15) ~f:(fun v -> MExact v));
      (1., G.return MWild);
      (2.,
       let%map v = Int.gen_incl 0 15 and m = Int.gen_incl 0 15 in
       MMask (v, m)) ]

let g_prio = G.of_list [50; 100; 150]

let g_rowd =
  let%map kf = g_mtch and jf = g_mtch and nv = Int.gen_incl 0 15 and prio = g_prio in
  {kf; jf; nv; prio}

let g_growd =
  let%map nf = g_mtch and pv = Int.gen_incl 0 15 and gprio = g_prio in
  {nf; pv; gprio}

let g_src =
  G.weighted_union
    [ (3., G.return SrcA);
      (3., G.return SrcB);
      (2., G.map (Int.gen_incl 0 3) ~f:(fun i -> SrcPrev i)) ]

let g_kop =
  G.union
    [ G.return KDelJ;
      G.return KWildK;
      G.return KProjK;
      G.return KSetJK;
      G.map (Int.gen_incl 0 15) ~f:(fun v -> KCube v) ]

let g_dop = G.of_list [DRen; DCopy; DDel]

let g_shape =
  G.weighted_union
    [ (3.,
       let%map s = g_src
       and kops = g_list_between 0 3 g_kop
       and dops = g_list_between 0 3 g_dop in
       Chain (s, kops, dops));
      (2.,
       let%map s1 = g_src and s2 = g_src and kops = g_list_between 0 2 g_kop in
       Both (s1, s2, kops));
      (3.,
       let%map s = g_src and kops = g_list_between 0 2 g_kop in
       Comp (s, kops));
      (2.,
       let%map s1 = g_src and s2 = g_src in
       Joined (s1, s2)) ]

let g_step =
  let%map shadow = G.weighted_union [(5., G.return false); (1., G.return true)]
  and shape = g_shape in
  {shadow; shape}

let g_upd =
  G.weighted_union
    [ (3.,
       let%map to_a = Bool.quickcheck_generator and r = g_rowd in
       UIns (to_a, r));
      (2., G.map g_growd ~f:(fun r -> UInsG r));
      (2.,
       let%map t = G.of_list [TA; TB; TG] and i = Int.gen_incl 0 7 in
       UDel (t, i)) ]

let g_case =
  let%map prog = g_list_between 1 3 g_step
  and a0 = g_list_between 0 3 g_rowd
  and b0 = g_list_between 0 3 g_rowd
  and g0 = g_list_between 0 3 g_growd
  and batches = g_list_between 1 5 (g_list_between 1 3 g_upd) in
  {prog; a0; b0; g0; batches}

(* ------------------------------------------------------------------ *)

let test_equivalence () =
  Quickcheck.test ~trials:300 ~sexp_of:[%sexp_of: case] g_case ~f:run_case

let () =
  Alcotest.run "incremental-quickcheck"
    [
      ( "equivalence",
        [
          Alcotest.test_case
            "incremental == monolithic on 300 random programs/updates" `Quick
            test_equivalence;
        ] );
    ]
