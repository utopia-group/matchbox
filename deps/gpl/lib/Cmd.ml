open Core
open Primitives

module Make (P : Primitive) = struct

  module Cmd = struct
    type t =
      | Prim of P.t
      | Seq of t list
      | Choice of t list
      [@@deriving equal]
    let prim prim = Prim prim
    let assume phi = prim @@ P.assume phi
    let assert_ phi = prim @@ P.assert_ phi
    let skip = prim @@ P.assume BExpr.true_
    let pass = prim @@ P.assert_ BExpr.true_
    let dead = prim @@ P.assume BExpr.false_
    let abort = prim @@ P.assert_ BExpr.false_

    let rec to_string_aux indent (c : t) : string =
      let open Printf in
      let space = Util.space indent in
      match c with
      | Prim p ->
        sprintf "%s %s" space (P.to_smtlib p)
      | Seq cs ->
        List.map cs ~f:(to_string_aux indent)
        |> String.concat ~sep:(sprintf ";\n")
      | Choice chxs ->
        List.map chxs
          ~f:(fun c ->
              sprintf "{\n%s\n%s}" (to_string_aux (indent+2) c) space)
        |> String.concat ~sep:(sprintf " [] ")
        |> Printf.sprintf "%s%s" space

    let to_string = to_string_aux 0

    let flatten_seqs cs : t list =
      let open List.Let_syntax in
      match%bind cs with
      | Prim _ as c -> return c
      | Choice _ as c -> return c
      | Seq cs -> cs

    let sequence cs =
      let cs = flatten_seqs cs in
      let cs = List.remove_consecutive_duplicates cs ~which_to_keep:`First ~equal in
      (* match List.find cs ~f:is_mult_annihil with *)
      (* | Some p -> p *)
      (* | None -> *)
        (* if List.exists2_exn cs cs ~f:(contra) then *)
        (*   abort *)
        (* else *)
          match cs with
          | [] -> skip
          | [c] -> c
          | _ -> Seq cs

    let sequence_map cs ~f =
      List.map ~f cs
      |> sequence

    let seq c1 c2 =
      match c1, c2 with
      | Seq c1s, Seq c2s ->
        c2s
        |> List.rev_append @@ List.rev c1s
        |> sequence
      | Seq c1s, _ ->
        List.rev c1s
        |> List.cons c2
        |> List.rev
        |> sequence
      | _, Seq c2s ->
        c1 :: c2s
        |> sequence
      | _, _ ->
        sequence [c1; c2]

    let choices cs : t =
      if List.is_empty cs then
        failwith "[Cmd.choices] cannot construct 0-ary choice"
      else
        Choice cs

    let choice c1 c2 = choices [c1;c2]

    let choice_seq cs1 cs2 = choice (sequence cs1) (sequence cs2)

    let choice_seqs cs = List.map cs ~f:sequence |> choices

    let choices_map cs ~f =
      List.map ~f cs
      |> choices

    (**/ END Smart Constructors*)

    let is_primitive (c : t) =
      match c with
      | Prim _ -> true
      | _ -> false

  end

  include Cmd

end
