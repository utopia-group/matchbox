open Core
open Semantics
open BaseLogic

(* Incremental (delta-propagating) evaluation of a [BaseLogic.t list].

   Instead of re-running [BaseInterpreter.eval_program] after every runtime
   rule update, we materialize every table as a rank-keyed map
   ([MatchAction.t Map.M(Rank).t]) and push row-level deltas
   ({inserts, deletes}) through the clause tree. [Rank.t] is constructed so
   that [Map.data] reproduces the exact row order [eval_inner] would emit,
   which keeps first-match-wins semantics (and hence [Compose]) sound.

   Every [Clause.t] node keeps a cache of its previous materialization,
   addressed by [(step index, path within the clause tree)]. A node whose
   inputs all have empty deltas returns its cache untouched, so subtrees
   unaffected by an update cost nothing beyond the tree walk.

   Bootstrap reuses the same machinery: the initial config rows are fed in as
   one big insert batch against empty caches, so there is exactly one
   evaluation code path. *)

module DTable = struct
  type t = MatchAction.t Map.M(Rank).t

  let empty : t = Map.empty (module Rank)

  (* Ascending rank order *is* the table order. *)
  let materialize : t -> MatchActionTable.t = Map.data
end

module Delta = struct
  type t = {
    ins : (Rank.t * MatchAction.t) list;
    del : (Rank.t * MatchAction.t) list;
  }

  let empty = {ins = []; del = []}
  let is_empty d = List.is_empty d.ins && List.is_empty d.del

  let sort d =
    let compare (r1, _) (r2, _) = Rank.compare r1 r2 in
    {ins = List.sort d.ins ~compare; del = List.sort d.del ~compare}

  (* Cancel insert/delete pairs at the same rank. Only used on *base-table*
     deltas, where equal ranks imply equal rows (seqs are never reused), so
     this is exactly "a row inserted and deleted within one batch". Node
     deltas must NOT be cancelled: [Compose] legitimately emits a delete and
     an insert at the same rank to express an in-place row change. *)
  let cancel d =
    let ranks l = List.map l ~f:fst |> Set.of_list (module Rank) in
    let both = Set.inter (ranks d.ins) (ranks d.del) in
    let keep = List.filter ~f:(fun (r, _) -> not (Set.mem both r)) in
    {ins = keep d.ins; del = keep d.del}

  let to_string d =
    let line pre (r, row) =
      sprintf "  %s [%s] %s" pre (Rank.to_string r) (MatchAction.to_string row)
    in
    List.map d.del ~f:(line "-") @ List.map d.ins ~f:(line "+")
    |> String.concat ~sep:"\n"
end

(* Address of a clause node: (step index, path of child indices, innermost
   first). Stable across rounds for a fixed program. *)
module Key = struct
  module T = struct
    type t = int * int list [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

type state = {
  caches : DTable.t Map.M(Key).t;     (* per clause node materialization *)
  nonces : BaseInterpreter.NonceState.t Map.M(Key).t;  (* MapOut Nonce nodes *)
  step_tables : DTable.t Int.Map.t;   (* each step's latest output *)
  base_tables : DTable.t String.Map.t;(* config-fed tables, rank-keyed *)
  seqs : int String.Map.t;            (* per-base-table next insertion seq *)
}

let empty_state = {
  caches = Map.empty (module Key);
  nonces = Map.empty (module Key);
  step_tables = Int.Map.empty;
  base_tables = String.Map.empty;
  seqs = String.Map.empty;
}

(* Deletes first, then inserts: a node may emit both at one rank to express
   an in-place change. [add_exn] guards the rank-uniqueness invariant. *)
let apply_delta (t : DTable.t) (d : Delta.t) : DTable.t =
  let t = List.fold d.del ~init:t ~f:(fun t (r, _) -> Map.remove t r) in
  List.fold d.ins ~init:t ~f:(fun t (r, row) -> Map.add_exn t ~key:r ~data:row)

let cache_old st key =
  Map.find st.caches key |> Option.value ~default:DTable.empty

(* The environment maps a symbol to its current version's
   (old table, new table, this-round delta) -- "current" in the sense of
   [eval_program]'s fold: base value until a step (re)defines the name. *)
type env = (DTable.t * DTable.t * Delta.t) String.Map.t

let rec eval_node (st : state) ~(key : Key.t) (clause : Clause.t) ~(env : env)
  : state * (DTable.t * DTable.t * Delta.t) =
  let child i = (fst key, i :: snd key) in
  let finish st old delta =
    let delta = Delta.sort delta in
    let new_ = apply_delta old delta in
    let st = {st with caches = Map.set st.caches ~key ~data:new_} in
    (st, (old, new_, delta))
  in
  match clause with
  | Id (f, _) -> (
    (* Missing symbol: [BaseInterpreter.get_mat] silently yields [] -- match it. *)
    match Map.find env (Symbol.to_string f) with
    | Some triple -> (st, triple)
    | None -> (st, (DTable.empty, DTable.empty, Delta.empty)))
  | Table (_, mat, _) ->
    (* Literal tables are constant: populate the cache once (bootstrap),
       empty delta ever after. *)
    if Map.mem st.caches key then
      let old = Map.find_exn st.caches key in
      (st, (old, old, Delta.empty))
    else
      let ins = List.mapi mat ~f:(fun i row -> (Rank.pos i, row)) in
      finish st DTable.empty {ins; del = []}
  | Override (f, g, _) ->
    let st, (_, _, fd) = eval_node st ~key:(child 0) f ~env in
    let st, (_, _, gd) = eval_node st ~key:(child 1) g ~env in
    let old = cache_old st key in
    if Delta.(is_empty fd && is_empty gd) then (st, (old, old, Delta.empty))
    else
      (* f_mat @ g_mat: re-key the children's deltas onto disjoint sides. *)
      let rekey s = List.map ~f:(fun (r, row) -> (Rank.side s r, row)) in
      finish st old
        Delta.
          {
            ins = rekey 0 fd.ins @ rekey 1 gd.ins;
            del = rekey 0 fd.del @ rekey 1 gd.del;
          }
  | Join (f, g, _) ->
    let st, (f_old, _, fd) = eval_node st ~key:(child 0) f ~env in
    let st, (g_old, g_new, gd) = eval_node st ~key:(child 1) g ~env in
    let old = cache_old st key in
    if Delta.(is_empty fd && is_empty gd) then (st, (old, old, Delta.empty))
    else
      (* Bilinear rule, keyed by rank pairs so the Δf x Δg corner cannot be
         double counted: [f_kept] excludes Δf's deletions, hence
           ins = Δf.ins x g_new  ∪  f_kept x Δg.ins
           del = Δf.del x g_old  ∪  f_kept x Δg.del   (∩ previous pairs)
         [Δf.ins x g_new] already contains [Δf.ins x Δg.ins]. *)
      let f_kept =
        List.fold fd.del ~init:f_old ~f:(fun t (r, _) -> Map.remove t r)
      in
      let mk_pairs lhs rhs =
        List.concat_map lhs ~f:(fun (rf, fr) ->
          List.filter_map rhs ~f:(fun (rg, gr) ->
            MatchAction.pair fr gr
            |> Option.map ~f:(fun row -> (Rank.pair rf rg, row))))
      in
      let ins =
        mk_pairs fd.ins (Map.to_alist g_new)
        @ mk_pairs (Map.to_alist f_kept) gd.ins
      in
      let del_keys =
        List.concat_map fd.del ~f:(fun (rf, _) ->
          List.map (Map.keys g_old) ~f:(Rank.pair rf))
        @ List.concat_map gd.del ~f:(fun (rg, _) ->
            List.map (Map.keys f_kept) ~f:(fun rf -> Rank.pair rf rg))
      in
      (* Pairs whose matches never intersected are not in the cache; skip. *)
      let del =
        List.filter_map del_keys ~f:(fun k ->
          Map.find old k |> Option.map ~f:(fun row -> (k, row)))
      in
      finish st old {ins; del}
  | Compose (f, g, _) ->
    (* g before f, mirroring [eval_inner]'s threading order. *)
    let st, (_, g_new, gd) = eval_node st ~key:(child 1) g ~env in
    let st, (_, f_new, fd) = eval_node st ~key:(child 0) f ~env in
    let old = cache_old st key in
    if Delta.(is_empty fd && is_empty gd) then (st, (old, old, Delta.empty))
    else
      (* First-match lookup straight off the rank map (= priority order),
         without materializing g. Same failure as [MatchActionTable.run]. *)
      let run_g data =
        With_return.with_return (fun ret ->
          Map.iteri g_new ~f:(fun ~key:_ ~data:(row : MatchAction.t) ->
            if MatchAction.does_match data row then
              ret.return (row.action, row.data));
          failwith "Couldnt find any matching rows in table")
      in
      let compose_row rf (row : MatchAction.t) =
        let action, data = run_g row.data in
        (rf, MatchAction.{row with action; data})
      in
      (* Δf: composition is 1-to-1 in f's rows and ranks. *)
      let ins_f = List.map fd.ins ~f:(fun (rf, row) -> compose_row rf row) in
      let del_f = List.map fd.del ~f:(fun (rf, _) -> (rf, Map.find_exn old rf)) in
      (* Δg: a first-match lookup for key k changes only if a changed g row
         matches k -- an inserted row can become k's first match only if it
         matches k, and a deleted row can have been k's first match only if
         it matched k. So the candidate set is exactly the f rows whose data
         is accepted by some inserted/deleted g row; recompute those and emit
         an in-place change where the result differs. *)
      let handled =
        List.map fd.ins ~f:fst @ List.map fd.del ~f:fst
        |> Set.of_list (module Rank)
      in
      let changed_g = List.map (gd.ins @ gd.del) ~f:snd in
      let del_g, ins_g =
        if List.is_empty changed_g then ([], [])
        else
          Map.fold f_new ~init:([], [])
            ~f:(fun ~key:rf ~data:(frow : MatchAction.t) (dels, inss) ->
              if Set.mem handled rf then (dels, inss)
              else if
                List.exists changed_g ~f:(fun gr ->
                  MatchAction.does_match frow.data gr)
              then
                let _, new_row = compose_row rf frow in
                let old_row = Map.find_exn old rf in
                if MatchAction.equal old_row new_row then (dels, inss)
                else ((rf, old_row) :: dels, (rf, new_row) :: inss)
              else (dels, inss))
      in
      finish st old {ins = ins_f @ ins_g; del = del_f @ del_g}
  | MapOut (f, tfx, _) ->
    let st, (_, _, fd) = eval_node st ~key:(child 0) f ~env in
    let old = cache_old st key in
    if Delta.is_empty fd then (st, (old, old, Delta.empty))
    else
      (* 1-to-1, rank preserved. Nonce state is per node and advances only on
         inserts: values continue from where the table left off rather than
         being renumbered from zero like a from-scratch run would. *)
      let nonce =
        Map.find st.nonces key
        |> Option.value ~default:BaseInterpreter.NonceState.empty
      in
      let nonce, ins =
        List.fold_map fd.ins ~init:nonce ~f:(fun nonce (rf, row) ->
          let nonce, row = BaseInterpreter.apply_out_tfx nonce row tfx in
          (nonce, (rf, row)))
      in
      let del = List.map fd.del ~f:(fun (rf, _) -> (rf, Map.find_exn old rf)) in
      let st = {st with nonces = Map.set st.nonces ~key ~data:nonce} in
      finish st old {ins; del}
  | MapIn (f, tfx, _) ->
    let st, (_, _, fd) = eval_node st ~key:(child 0) f ~env in
    let old = cache_old st key in
    if Delta.is_empty fd then (st, (old, old, Delta.empty))
    else
      (* 1-to-0..n: outputs of the input at rank [rf] live at [Sub (rf, i)],
         so deleting an input deletes the contiguous rank range under it
         (covers Filter splits and CubeFilter drops uniformly). *)
      let ins =
        List.concat_map fd.ins ~f:(fun (rf, row) ->
          BaseInterpreter.apply_in_tfx row tfx
          |> List.mapi ~f:(fun i out -> (Rank.sub rf i, out)))
      in
      let del =
        List.concat_map fd.del ~f:(fun (rf, _) ->
          Map.fold_range_inclusive old ~min:(Rank.sub_lo rf)
            ~max:(Rank.sub_hi rf) ~init:[]
            ~f:(fun ~key ~data acc -> (key, data) :: acc))
      in
      finish st old {ins; del}

(* ------------------------------------------------------------------ *)
(* Updates                                                             *)
(* ------------------------------------------------------------------ *)

type op =
  | Insert of {table : string; row : MatchAction.t; priority : int}
  | Delete of {table : string; matches : MatchExpression.t; priority : int}

let op_to_string = function
  | Insert {table; row; priority} ->
    sprintf "insert %s prio=%d %s" table priority (MatchAction.to_string row)
  | Delete {table; matches; priority} ->
    let ms =
      Map.to_alist matches
      |> List.map ~f:(fun (x, m) -> sprintf "%s~%s" x (Match.to_string m))
      |> String.concat ~sep:", "
    in
    sprintf "delete %s prio=%d (%s)" table priority ms

let add_to_delta deltas table ~f =
  Map.update deltas table ~f:(fun d -> f (Option.value d ~default:Delta.empty))

(* Apply one op to the base tables, accumulating the per-table delta. *)
let apply_op ~strict (st, deltas) op =
  match op with
  | Insert {table; row; priority} ->
    let seq = Map.find st.seqs table |> Option.value ~default:0 in
    let rank = Rank.base ~prio:priority ~seq in
    let tbl =
      Map.find st.base_tables table |> Option.value ~default:DTable.empty
    in
    let tbl = Map.add_exn tbl ~key:rank ~data:row in
    ( { st with
        base_tables = Map.set st.base_tables ~key:table ~data:tbl;
        seqs = Map.set st.seqs ~key:table ~data:(seq + 1);
      },
      add_to_delta deltas table ~f:(fun d ->
        {d with ins = (rank, row) :: d.ins}) )
  | Delete {table; matches; priority} -> (
    let tbl =
      Map.find st.base_tables table |> Option.value ~default:DTable.empty
    in
    (* The row to delete is identified by priority + per-field equal matches;
       on a tie, the lowest rank (first arrival) goes. *)
    let found =
      Map.to_sequence tbl
      |> Sequence.find ~f:(fun ((rank : Rank.t), (row : MatchAction.t)) ->
           match rank with
           | Base (p, _) ->
             p = priority && Map.equal Match.equal row.matches matches
           | _ -> false)
    in
    match found with
    | Some (rank, row) ->
      let tbl = Map.remove tbl rank in
      ( {st with base_tables = Map.set st.base_tables ~key:table ~data:tbl},
        add_to_delta deltas table ~f:(fun d ->
          {d with del = (rank, row) :: d.del}) )
    | None ->
      let msg =
        sprintf "delete found no matching row: %s" (op_to_string op)
      in
      if strict then failwith msg
      else (
        eprintf "warning: %s (skipped)\n%!" msg;
        (st, deltas)))

(* One atomic batch: mutate the base tables, then fold the program forward,
   mirroring [BaseInterpreter.eval_program]'s [Config.set] fold so that base
   names shadowed by a step resolve to the right version. Returns the
   per-step output deltas in program order. *)
let apply_batch ?(strict = false) (st : state) (prog : BaseLogic.t list)
    (ops : op list) : state * (string * Delta.t) list =
  let pre = st.base_tables in
  let st, base_deltas =
    List.fold ops ~init:(st, String.Map.empty) ~f:(apply_op ~strict)
  in
  let base_deltas = Map.map base_deltas ~f:(fun d -> Delta.(sort (cancel d))) in
  let env =
    Map.fold st.base_tables ~init:String.Map.empty
      ~f:(fun ~key:name ~data:new_ env ->
        let old = Map.find pre name |> Option.value ~default:DTable.empty in
        let d =
          Map.find base_deltas name |> Option.value ~default:Delta.empty
        in
        Map.set env ~key:name ~data:(old, new_, d))
  in
  let (st, _), rev_deltas =
    List.foldi prog ~init:((st, env), [])
      ~f:(fun i ((st, env), acc) {defined; definition} ->
        let st, ((_, new_, delta) as triple) =
          eval_node st ~key:(i, []) definition ~env
        in
        let st =
          {st with step_tables = Map.set st.step_tables ~key:i ~data:new_}
        in
        let env = Map.set env ~key:defined.name ~data:triple in
        ((st, env), (defined.name, delta) :: acc))
  in
  (st, List.rev rev_deltas)

(* Bootstrap: feed every initial config row through the incremental
   evaluator as an insert into empty state. [rows] must be the *raw* parsed
   rows (with priorities), e.g. from [RuntimeInterface] -- the materialized
   [Config.t] has already dropped them. *)
let bootstrap (prog : BaseLogic.t list)
    (rows : (string * MatchAction.t * int) list) : state =
  let ops =
    List.map rows ~f:(fun (table, row, priority) -> Insert {table; row; priority})
  in
  let st, _ = apply_batch ~strict:true empty_state prog ops in
  st

(* ------------------------------------------------------------------ *)
(* Introspection (CLI / --check / tests)                               *)
(* ------------------------------------------------------------------ *)

let derived_names (prog : BaseLogic.t list) : String.Set.t =
  List.map prog ~f:(fun s -> s.defined.name) |> String.Set.of_list

let base_config (st : state) : Config.t =
  Map.fold st.base_tables ~init:Config.empty ~f:(fun ~key ~data cfg ->
    Config.set cfg key (DTable.materialize data))

let step_table_exn (st : state) (i : int) : MatchActionTable.t =
  Map.find_exn st.step_tables i |> DTable.materialize

(* Per program-order step: does the incremental materialization equal a
   from-scratch [eval_program] on the current base tables? *)
let verify_against_full (st : state) (prog : BaseLogic.t list) :
    (string * bool) list =
  let results, _ = BaseInterpreter.eval_program (base_config st) prog in
  List.mapi results ~f:(fun i (name, full_table) ->
    (name, MatchActionTable.equal full_table (step_table_exn st i)))

let rec clause_has_nonce : Clause.t -> bool = function
  | Id _ | Table _ -> false
  | Join (f, g, _) | Override (f, g, _) | Compose (f, g, _) ->
    clause_has_nonce f || clause_has_nonce g
  | MapOut (_, OutTfx.Nonce _, _) -> true
  | MapOut (f, _, _) | MapIn (f, _, _) -> clause_has_nonce f

let has_nonce (prog : BaseLogic.t list) : bool =
  List.exists prog ~f:(fun s -> clause_has_nonce s.definition)

(* ------------------------------------------------------------------ *)
(* Update-file parsing (JSON)                                          *)
(*                                                                     *)
(* The updates file is a JSON list; each element is either one op      *)
(* object or a list of op objects forming one atomic batch:            *)
(*   {"op": "insert" (default), <RuntimeInterface.Insertion fields>}   *)
(*   {"op": "delete", "table": t, "matches": {..}, "priority": p}      *)
(* ------------------------------------------------------------------ *)

let parse_op (typs : Type.ctx) ~(derived : String.Set.t)
    (json : Yojson.Safe.t) : op =
  let module I = RuntimeInterface.Insertion in
  match json with
  | `Assoc dict ->
    let field name = List.Assoc.find dict name ~equal:String.equal in
    let kind =
      match field "op" with
      | None | Some (`String "insert") -> `Ins
      | Some (`String "delete") -> `Del
      | Some j ->
        failwithf "unknown op %s (expected \"insert\" or \"delete\")"
          (Yojson.Safe.to_string j) ()
    in
    let table =
      match field "table" with
      | Some (`String t) -> t
      | _ -> failwith "update is missing a \"table\" field"
    in
    if Set.mem derived table then
      failwithf
        "cannot update table %s: it is defined by the program, not a base table"
        table ();
    let ttyp =
      match Map.find typs table with
      | Some t -> t
      | None -> failwithf "unknown table %s" table ()
    in
    (match kind with
     | `Ins -> (
       let clean =
         `Assoc (List.filter dict ~f:(fun (k, _) -> String.(k <> "op")))
       in
       match I.convert_row typs clean with
       | Some (table, row, priority) -> Insert {table; row; priority}
       | None -> failwithf "malformed insert: %s" (Yojson.Safe.to_string json) ())
     | `Del ->
       let matches =
         match field "matches" with
         | Some m -> I.convert_match ttyp m
         | None -> failwith "delete is missing a \"matches\" field"
       in
       let priority =
         match field "priority" with
         | Some p -> I.convert_prio p
         | None -> failwith "delete is missing a \"priority\" field"
       in
       Delete {table; matches; priority})
  | _ ->
    failwithf "expected an update object, got %s" (Yojson.Safe.to_string json) ()

let parse_updates_file (typs : Type.ctx) ~(derived : String.Set.t)
    (filename : string) : op list list =
  match Yojson.Safe.from_file filename with
  | `List items ->
    List.map items ~f:(function
      | `List batch -> List.map batch ~f:(parse_op typs ~derived)
      | obj -> [parse_op typs ~derived obj])
  | json ->
    failwithf "expected the updates file to be a JSON list, got %s"
      (Yojson.Safe.to_string json) ()
