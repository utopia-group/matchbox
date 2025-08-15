open Core
open Semantics
open Ke

(* Representing switch state *)
type switch = {
  id : Bit.Vector.t; (* the address *)
  ports : Bit.Vector.t list;
  tables : MatchActionTable.t Map.M(String).t;
}

type loc = { switch : Bit.Vector.t; port : Bit.Vector.t } [@@deriving equal]

(* Controller state: multiple switches *)
type t = { switches : switch list; links : (loc * loc) list }

let create () = { switches = []; links = [] }

let find_switch (st : t) (sid : Bit.Vector.t) : switch option =
  List.find st.switches ~f:(fun s -> Bit.Vector.equal s.id sid)

let replace_switch (st : t) (sw : switch) : t =
  {
    st with
    switches =
      List.map st.switches ~f:(fun sw' ->
        if Bit.Vector.equal sw'.id sw.id then sw else sw');
  }

let make_forward_rule ~(dst_bv : Bit.Vector.t) ~(egress_port : Bit.Vector.t) : MatchAction.t =
  let matches = Map.singleton (module String) "dst" (Match.Ternary (Trit.Vector.of_bv dst_bv)) in
  let action = Action.make "fwd" (Map.singleton (module String) "port" egress_port) in
  MatchAction.make matches action

let make_drop_rule ~(dst_width : int) : MatchAction.t =
  let matches = Map.singleton (module String) "dst" (Match.catch_all dst_width) in
  let action = Action.nullary "drop" in
  MatchAction.make matches action

let upsert_forward_rule (sw : switch) ~(dst_bv : Bit.Vector.t) ~(egress_port : Bit.Vector.t) : switch =
  let row_new = make_forward_rule ~dst_bv ~egress_port in
  let tbl = Option.value ~default:[] (Map.find sw.tables "Route") in
  (* Remove any existing rule with same dst match, then add new one at the front. *)
  let tbl_filtered =
    List.filter tbl ~f:(fun row ->
      not (Match.equal (MatchAction.get_match row "dst") (Match.exact dst_bv)))
  in
  let tbl' = MatchActionTable.(tbl_filtered <+ [row_new]) in
  let tables' = Map.set sw.tables ~key:"Route" ~data:tbl' in
  { sw with tables = tables' }

let nexts (st : t) (sid : Bit.Vector.t) : (Bit.Vector.t * Bit.Vector.t) list =
  List.filter_map st.links ~f:(fun (src, dst) ->
    if Bit.Vector.equal src.switch sid then Some (dst.switch, src.port)
    else None)

(* BFS to find the shortest path from src_id to dst_id over directed links.
   Returns a mapping to construct the next-hop port per switch:
   came_from[next] = (prev, prev_port). *)
let find_shortest_path (st : t) ~(src_id : Bit.Vector.t) ~(dst_id : Bit.Vector.t)
  : (Bit.Vector.t * (Bit.Vector.t * Bit.Vector.t)) list option =
  let rec step
    (q : Bit.Vector.t Fke.t)
    (visited : Bit.Vector.t list)
    (came_from : (Bit.Vector.t * (Bit.Vector.t * Bit.Vector.t)) list)
    : (Bit.Vector.t * (Bit.Vector.t * Bit.Vector.t)) list option =
    match Fke.pop q with
    | None -> None
    | Some (u, q') ->
      if Bit.Vector.equal u dst_id then Some came_from
      else
        let nbrs = nexts st u in
        let q_next, visited', came_from', found =
          List.fold nbrs
            ~init:(q', visited, came_from, false)
            ~f:(fun ((q_acc, vis_acc, cf_acc, found_acc) as acc) (v, out_port) ->
              if List.exists vis_acc ~f:(Bit.Vector.equal v) then acc
              else
                let vis' = v :: vis_acc in
                let cf'  = (v, (u, out_port)) :: cf_acc in
                let q''  = Fke.push q_acc v in
                let found' = found_acc || Bit.Vector.equal v dst_id in
                (q'', vis', cf', found'))
        in
        if found then Some came_from' else step q_next visited' came_from'
  in
  step (Fke.push Fke.empty src_id) [src_id] []

(* --- Message Handlers --- *)

let switch_on (st : t) (sid : Bit.Vector.t) (ports : Bit.Vector.t list) : t =
  printf
    "Received Hello from switch %s with the following active ports: %s\n%!"
    (Bit.Vector.to_string sid)
    (ports |> List.map ~f:Bit.Vector.to_string |> String.concat ~sep:" ");
  match find_switch st sid with
  | None ->
    let sw = {
        id = sid;
        ports;
        tables =
          Map.singleton (module String) "Route"
            [make_drop_rule ~dst_width:(Bit.Vector.length sid)]
      }
    in
    {
      st with
      switches = sw :: st.switches;
    }
  | Some s -> replace_switch st { s with ports }

let switch_off (state : t) (sid : Bit.Vector.t) : t =
  (* A switch has disconnected from the network *)
  printf "Received Goodbye from switch %s\n%!" (Bit.Vector.to_string sid);
  let switches =
    List.filter state.switches ~f:(fun sw ->
      not (Bit.Vector.equal sw.id sid))
  in
  let links =
    List.filter state.links ~f:(fun (src, dst) ->
      not (Bit.Vector.equal src.switch sid
        || Bit.Vector.equal dst.switch sid))
  in
  { switches; links }

let link_up (st : t) (sw : switch) (src : loc) (dst : loc) : t =
  (* You have received a message from [switch] saying that there is a link (think ethernet cable) 
     between connecting switch with id [src.id] to switch with id [dst.id] via ports [src.port] and [dst.port]
     generally, we can assume that links are unidirectional (this has to do with queues) *)
  printf "According to %s, (%s@%s) is connected to (%s@%s)\n%!"
    (Bit.Vector.to_string sw.id)
    (Bit.Vector.to_string src.switch)
    (Bit.Vector.to_string src.port)
    (Bit.Vector.to_string dst.switch)
    (Bit.Vector.to_string dst.port);
  if
    List.exists st.links ~f:(fun (src', dst') ->
      equal_loc src' src && equal_loc dst' dst)
  then st
  else { st with links = (src, dst) :: st.links }

let link_down (st : t) (sw : switch) (src : loc) (dst : loc) : t =
  (* You have received a message from [switch] saying that the previously established link between src and dst is offline *)
  printf "According to %s, (%s@%s) is connected to (%s@%s)\n%!"
    (Bit.Vector.to_string sw.id)
    (Bit.Vector.to_string src.switch)
    (Bit.Vector.to_string src.port)
    (Bit.Vector.to_string dst.switch)
    (Bit.Vector.to_string dst.port);
  {
    st with
    links =
      List.filter st.links ~f:(fun (src', dst') ->
        not (equal_loc src' src && equal_loc dst' dst));
  }

let packet_in (st : t) (sid : Bit.Vector.t) (packet : Bit.Vector.t Map.M(String).t) : t =
  (* Handler for when a switch doesn't know what to do with a packet, that is, it needs a new route.
     Extract the relevant data from the packet (e.g. its source and target destination addresses).
     Update the match-action tables to route the packet as requested. *)
  match find_switch st sid with
  | None ->
    printf "Packet-In from unknown switch %s\n%!" (Bit.Vector.to_string sid);
    st
  | Some switch -> (
    printf "Packet-In from switch %s\n%!" (Bit.Vector.to_string switch.id);
    match Map.find packet "dst" with
    | None ->
      printf "Packet missing \"dst\" field, ignoring\n%!";
      st
    | Some dst_bv -> (
      if Bit.Vector.equal dst_bv sid then (
        printf
          "Packet is already at destination %s, no routing needed\n%!"
          (Bit.Vector.to_string dst_bv);
        st)
      else
        match find_switch st dst_bv with
        | None ->
          printf
            "No known switch with id %s; cannot route\n%!"
            (Bit.Vector.to_string dst_bv);
          st
        | Some _ -> (
          match find_shortest_path st ~src_id:sid ~dst_id:dst_bv with
          | None ->
            printf
              "No path from %s -> %s, cannot route\n%!"
              (Bit.Vector.to_string sid)
              (Bit.Vector.to_string dst_bv);
            st
          | Some came_from ->
            let hops = 
              List.fold came_from ~init:[] ~f:(fun acc (sid', (prev, prev_port)) ->
                if Bit.Vector.equal sid' sid then acc
                else (prev, prev_port) :: acc)
            in
            let st' = List.fold hops ~init:st ~f:(
              fun acc_st (sid, sw_port) ->
                match find_switch acc_st sid with
                | None -> acc_st
                | Some sw ->
                  sw
                  |> upsert_forward_rule ~dst_bv ~egress_port:sw_port
                  |> replace_switch acc_st)
            in
            printf
              "Set up forwarding for dst=%s across %d hop(s)\n%!"
              (Bit.Vector.to_string dst_bv)
              (List.length hops);
            st')))
