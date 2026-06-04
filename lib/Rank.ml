open Core

(* A [Rank.t] is a lexicographic position key for a row of a materialized
   table. Ranks let the incremental evaluator ([Incremental]) store each
   table as a [Map.M(Rank)] whose [Map.data] (ascending key order) is exactly
   the row list that [BaseInterpreter.eval_inner] would produce. Order is
   semantically load-bearing: tables are first-match-wins, so an incremental
   scheme that only tracked row *sets* would be unsound under [Compose].

   Constructors mirror how each [BaseLogic.Clause.t] operator arranges its
   output rows (the derived structural compare is lexicographic):
   - [Base (priority, seq)]: a base-table row. [RuntimeInterface.convert_trace]
     sorts config rows ascending by priority; [seq] breaks ties by arrival
     order and makes ranks unique.
   - [Pos i]: the [i]th row of a [Table] literal.
   - [Side (s, r)]: [Override (f, g)] is [f_mat @ g_mat], so f-rows get
     [Side (0, r)] and g-rows [Side (1, r)] -- every f-row sorts first.
   - [Sub (r, i)]: [MapIn] maps one input row to 0..n output rows (e.g.
     [Filter] splits); the [i]th output of the input at rank [r]. 1-to-1
     transforms always use [Sub (r, 0)] so a node's key space is uniform.
   - [Pair (rf, rg)]: [Join (f, g)] emits pairs f-major/g-minor.

   [MapOut] and [Compose] are 1-to-1 in the order of their first argument and
   reuse its ranks unchanged.

   Ranks within one table are unique by construction: sibling rows differ in
   the outermost index, and rows derived from different inputs differ in the
   nested child rank. *)

module T = struct
  type t =
    | Base of int * int
    | Pos of int
    | Side of int * t
    | Sub of t * int
    | Pair of t * t
  [@@deriving compare, sexp]
end

include T
include Comparable.Make (T)

let base ~prio ~seq = Base (prio, seq)
let pos i = Pos i
let side s r = Side (s, r)
let sub r i = Sub (r, i)
let pair rf rg = Pair (rf, rg)

(* Bounds for range-scanning all [Sub (parent, _)] keys of one parent: in a
   MapIn node's table every key is [Sub (p, i)], and the first component is
   compared first, so the inclusive interval [sub_lo p, sub_hi p] contains
   exactly the rows derived from [p]. *)
let sub_lo parent = Sub (parent, Int.min_value)
let sub_hi parent = Sub (parent, Int.max_value)

let rec to_string = function
  | Base (prio, seq) -> sprintf "%d.%d" prio seq
  | Pos i -> sprintf "#%d" i
  | Side (s, r) -> sprintf "%c%s" (if Int.(s = 0) then 'l' else 'r') (to_string r)
  | Sub (r, i) -> sprintf "%s:%d" (to_string r) i
  | Pair (rf, rg) -> sprintf "(%s,%s)" (to_string rf) (to_string rg)
