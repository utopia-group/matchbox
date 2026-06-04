open Core
open Matchbox
open Semantics

let addr_width = 16
let port_width = 8
let bv w n = Bit.Vector.of_int ~width:w n
let sid n = bv addr_width n
let port n = bv port_width n

let get_switch_exn (st : Controller.t) (id : Bit.Vector.t) : Controller.switch =
  List.find_exn st.switches ~f:(fun s -> Bit.Vector.equal s.id id)

let switch_on_with_ports (st : Controller.t) (id : Bit.Vector.t) (port_ids : int list) : Controller.t =
  Controller.switch_on st id (List.map port_ids ~f:port)

let link_up_by_ids (st : Controller.t) ~(reporter : Bit.Vector.t)
    ~(src_sw : Bit.Vector.t) ~(src_pt : Bit.Vector.t) ~(dst_sw : Bit.Vector.t)
    ~(dst_pt : Bit.Vector.t) : Controller.t =
  let reporter_sw = get_switch_exn st reporter in
  let src = Controller.{ switch = src_sw; port = src_pt } in
  let dst = Controller.{ switch = dst_sw; port = dst_pt } in
  Controller.link_up st reporter_sw src dst

let add_bidir_link
  (st : Controller.t)
  ~(a : Bit.Vector.t) 
  ~(pa_out : int)
  ~(pa_in : int)
  ~(b : Bit.Vector.t)
  ~(pb_out : int)
  ~(pb_in : int)
  : Controller.t =
  let st =
    link_up_by_ids st ~reporter:a ~src_sw:a ~src_pt:(port pa_out) ~dst_sw:b
      ~dst_pt:(port pb_in)
  in
  link_up_by_ids st ~reporter:b ~src_sw:b ~src_pt:(port pb_out) ~dst_sw:a
    ~dst_pt:(port pa_in)

let boot_switches (n : int) : Controller.t =
  let base_ports = [ 1; 2; 3; 4; 5; 6; 7; 8 ] in
  List.fold
    (List.init n ~f:(fun i -> sid (i + 1)))
    ~init:(Controller.create ())
    ~f:(fun st sw_id -> switch_on_with_ports st sw_id base_ports)

let connect_line (st0 : Controller.t) (n : int) : Controller.t =
  let rec loop i st =
    if i >= n then st
    else
      let a = sid i in
      let b = sid (i + 1) in
      let st' = add_bidir_link st ~a ~pa_out:1 ~pa_in:2 ~b ~pb_out:2 ~pb_in:1 in
      loop (i + 1) st'
  in
  if n <= 1 then st0 else loop 1 st0

let connect_ring (st0 : Controller.t) (n : int) : Controller.t =
  if n <= 1 then st0
  else
    let rec loop i st =
      if i > n then st
      else
        let a = sid i in
        let b = sid (if i = n then 1 else i + 1) in
        let st' =
          add_bidir_link st ~a ~pa_out:1 ~pa_in:2 ~b ~pb_out:2 ~pb_in:1
        in
        loop (i + 1) st'
    in
    loop 1 st0

let find_forward_action (sw : Controller.switch) ~(dst : Bit.Vector.t) : Action.t option =
  match Map.find sw.tables "Route" with
  | None -> None
  | Some tbl ->
    tbl
    |> List.find ~f:(fun row ->
      String.(Action.get_name (MatchAction.get_action row) = "fwd") &&
      Semantics.Match.equal (MatchAction.get_match row "dst") (Semantics.Match.exact dst))
    |> Option.map ~f:MatchAction.get_action


let program_all_pairs (st0 : Controller.t) : Controller.t =
  let ids = List.map st0.switches ~f:(fun s -> s.id) in
  List.fold ids ~init:st0 ~f:(fun st src_id ->
    List.fold ids ~init:st ~f:(fun st' dst_id ->
      if Bit.Vector.equal src_id dst_id then st'
      else
        let pkt = String.Map.of_alist_exn [ ("dst", dst_id) ] in
        Controller.packet_in st' src_id pkt))

let check_int name = Alcotest.(check int) name
let check_bool name = Alcotest.(check bool) name
let check_opt_some name = Alcotest.(check bool) name true

let test_switch_lifecycle () =
  let st = Controller.create () in
  let s1 = sid 1 and s2 = sid 2 in
  let st = switch_on_with_ports st s1 [ 1; 2; 3 ] in
  let st = switch_on_with_ports st s2 [ 1; 2 ] in
  check_int "2 switches after switch_on" 2 (List.length st.switches);
  let st = Controller.switch_off st s1 in
  check_int "1 switch after switch_off" 1 (List.length st.switches)

let test_link_lifecycle () =
  let st = boot_switches 2 in
  let a = sid 1 and b = sid 2 in
  let st = add_bidir_link st ~a ~pa_out:1 ~pa_in:2 ~b ~pb_out:2 ~pb_in:1 in
  check_int "2 directed links after add_bidir_link" 2 (List.length st.links);
  (* Take one direction down *)
  let reporter = get_switch_exn st a in
  let src = Controller.{ switch = a; port = port 1 } in
  let dst = Controller.{ switch = b; port = port 1 } in
  let st = Controller.link_down st reporter src dst in
  check_int "1 directed link after link_down" 1 (List.length st.links)

let test_all_pairs_line () =
  let n = 5 in
  let st = boot_switches n |> Fn.flip connect_line n |> program_all_pairs in
  let ids = List.map st.switches ~f:(fun s -> s.id) in
  (* Every src has a forward rule for every dst != src *)
  List.iter st.switches ~f:(fun sw ->
    List.iter ids ~f:(fun dst ->
      if not (Bit.Vector.equal sw.id dst) then
        match find_forward_action sw ~dst with
        | None -> Alcotest.fail "missing forward rule"
        | Some act ->
          Alcotest.(check string)
            "action name" "fwd" (Action.get_name act);
          ignore (Action.get_datum_exn act "port")))

let test_all_pairs_ring () =
  let n = 4 in
  let st = boot_switches n |> Fn.flip connect_ring n |> program_all_pairs in
  List.iter st.switches ~f:(fun sw ->
    List.iter st.switches ~f:(fun dst_sw ->
      if not (Bit.Vector.equal sw.id dst_sw.id) then
        check_opt_some "has forward rule"
          (Option.is_some (find_forward_action sw ~dst:dst_sw.id))))

let test_unknown_packet_in_no_crash () =
  let st = boot_switches 2 in
  let unknown = sid 999 in
  let pkt = Map.singleton (module String) "dst" (sid 1) in
  let st' = Controller.packet_in st unknown pkt in
  (* State unchanged: 2 switches, 0 links *)
  check_int "switch count unchanged" 2 (List.length st'.switches);
  check_int "link count unchanged" 0 (List.length st'.links)

let test_no_link_no_fwd_rule () =
  (* Two switches, no links; try to route from 1 -> 2: expect no forward rule on 1 *)
  let st = boot_switches 2 in
  let pkt = Map.singleton (module String) "dst"(sid 2) in
  let st = Controller.packet_in st (sid 1) pkt in
  let s1 = get_switch_exn st (sid 1) in
  let has_rule = Option.is_some (find_forward_action s1 ~dst:(sid 2)) in
  check_bool "no forward rule when no link" false has_rule
