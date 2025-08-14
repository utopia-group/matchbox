open Core
open Semantics

module Controller = struct
  (* Representing switch state *)
  
  type switch = {
    id : Bit.Vector.t; (* the address *)
    ports : Bit.Vector.t list;
    tables: MatchActionTable.t String.Map.t;
  }

  type loc = {
    switch : Bit.Vector.t;
    port : Bit.Vector.t;
  }

  (* Controller state: multiple switches *)
  type t = {
    switches : switch list;
    links : (loc * loc) list;
  }

  let create () = { switches = []; links = [] }

  (* --- Message Handlers --- *)

  let switch_on (state : t) (switch_id : Bit.Vector.t) (ports : Bit.Vector.t list) : t =
    (* A switch has connected to the network *)
    Printf.printf "Received Hello from switch %s: with the following active ports: %s\n%!" 
      (Bit.Vector.to_string switch_id) 
      (List.map ports ~f:Bit.Vector.to_string |> String.concat ~sep:" ");
    failwith "todo"

  let switch_off (state : t) (switch_id : Bit.Vector.t) : t = 
    (* A switch has disconnected from the network *)
    Printf.printf "Received Goodbye from switch %s\n%!" 
      (Bit.Vector.to_string switch_id);
    failwith "todo"


  
  let link_up (state : t) (switch : switch) (src : loc) (dst : loc) : t = 
    (* You have received a message from [switch] saying that there is a link (think ethernet cable) 
       between connecting switch with id [src.id] to switch with id [dst.id] via ports [src.port] and [dst.port]
       generally, we can assume that links are unidirectional (this has to do with queues) *)
    Printf.printf "According to %s, (%s@%s) is connected to (%s@%s)\n%!"
      (Bit.Vector.to_string switch.id)
      (Bit.Vector.to_string src.switch)
      (Bit.Vector.to_string src.port)
      (Bit.Vector.to_string dst.switch)
      (Bit.Vector.to_string dst.port);
    failwith "todo"

  let link_down (state : t) (switch : switch) (src : loc) (dst : loc) : t = 
    (* You have received a message from [switch] saying that the previously established link between src and dst is offline *)
    Printf.printf "According to %s, (%s@%s) is connected to (%s@%s)\n%!"
      (Bit.Vector.to_string switch.id)
      (Bit.Vector.to_string src.switch)
      (Bit.Vector.to_string src.port)
      (Bit.Vector.to_string dst.switch)
      (Bit.Vector.to_string dst.port);
    failwith "todo"

  let packet_in (state : t) (switch_id : Bit.Vector.t) (packet : Bit.Vector.t String.Map.t) : t =
    (* handler for when a switch doesn't know what to do with a packet, that is, it needs a new route *)
    (* Extract the relevant data from the packet (e.g. its source and target destination addresses.) *)
    (* update the match-action tables to route the packet as requested *)
    match List.find state.switches ~f:(fun switch -> Bit.Vector.equal switch.id switch_id) with
    | None -> 
      Printf.printf "Packet-In from unknown switch %s\n%!" (Bit.Vector.to_string switch_id);
      failwith "todo"
    | Some switch ->
      Printf.printf "Packet-In from switch %s\n%!"
      (Bit.Vector.to_string switch.id);
      failwith "todo"

end