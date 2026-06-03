open Core

(* A Hoare-style property about a single named match-action table:

     assert <table> : { <pre> } => { <post> } .

   [pre] is a boolean formula over the table's input *key* variables.
   [post] is a conjunction of *guarantees* over the table's output: either the
   special action variable [$action] equalling a particular action, or a boolean
   predicate over the output *data* fields (and/or keys).

   A program C satisfies the property (C |= P) iff, for every packet where [pre]
   holds, the table's first-match-wins output satisfies every guarantee in
   [post].  This is decided by [Verifier.check] via Z3. *)

type guarantee =
  | ActionEq of Semantics.MagmaAction.t   (* $action == drop  (or set_gid;fwd) *)
  | Pred of Gpl.BExpr.t                    (* e.g. port == 9[1], over data/keys *)

type t = {
  table : string;            (* the table this property constrains *)
  pre : Gpl.BExpr.t;         (* precondition over input keys *)
  post : guarantee list;     (* postcondition: conjunction of guarantees *)
}

let guarantee_to_string = function
  | ActionEq a -> Printf.sprintf "$action == %s" (Semantics.MagmaAction.to_string a)
  | Pred phi -> Gpl.BExpr.to_smtlib phi

let post_to_string (post : guarantee list) =
  match post with
  | [] -> "true"
  | _ -> List.map post ~f:guarantee_to_string |> String.concat ~sep:" && "

let to_string {table = _; pre; post} =
  Printf.sprintf "{ %s } => { %s }" (Gpl.BExpr.to_smtlib pre) (post_to_string post)
