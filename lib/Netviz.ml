(* netviz.ml
open Core
open Semantics
open Controller

module Netviz = struct
  let bv s = Bit.Vector.to_string s

  let port_label p =
    (* You can tweak how ports print here; using Bit.Vector string now *)
    "p" ^ Bit.Vector.to_string p

  let node_id (sid : Bit.Vector.t) =
    (* Make a DOT-safe identifier: use the bitvector string inside quotes *)
    "\"" ^ bv sid ^ "\""

  let node_label (sid : Bit.Vector.t) =
    (* Shown to the user (can include width etc if you want) *)
    bv sid

  let edge_label (src_p : Bit.Vector.t) (dst_p : Bit.Vector.t) =
    port_label src_p ^ "→" ^ port_label dst_p

  let to_dot (st : Controller.t) : string =
    let b = Buffer.create 1024 in
    let pf fmt = Printf.bprintf b fmt in
    pf "digraph G {\n";
    pf "  rankdir=LR;\n";
    pf "  node [shape=ellipse, fontname=\"Menlo\", fontsize=10];\n";
    pf "  edge [fontname=\"Menlo\", fontsize=9];\n";
    (* Nodes *)
    List.iter st.switches ~f:(fun (sw : Controller.switch) ->
      pf "  %s [label=\"%s\"];\n" (node_id sw.id) (node_label sw.id)
    );
    (* Directed links with port labels *)
    List.iter st.links ~f:(fun (src, dst) ->
      pf "  %s -> %s [label=\"%s\"];\n"
        (node_id src.switch) (node_id dst.switch)
        (edge_label src.port dst.port)
    );
    pf "}\n";
    Buffer.contents b

  let write_dot ~(filename : string) (st : Controller.t) : unit =
    Out_channel.write_all filename ~data:(to_dot st)

  (* Optional: render to PNG by invoking Graphviz's `dot` if present *)
  let render_png ?(engine="dot") ~(out_png : string) (st : Controller.t)
    : (unit, string) Result.t =
    let tmp_dot = Filename.temp_file "netviz_" ".dot" in
    Exn.protect
      ~f:(fun () ->
        write_dot ~filename:tmp_dot st;
        let prog = engine in  (* "dot", "neato", "sfdp", etc. *)
        let argv = [| prog; "-Tpng"; tmp_dot; "-o"; out_png |] in
        match Unix.fork_exec ~prog ~argv () with
        | pid ->
            let (_ : Unix.Process_status.t) = Unix.waitpid pid in
            if Sys_unix.file_exists out_png
            then Ok ()
            else Error (sprintf "Graphviz (%s) did not produce %s" engine out_png)
      )
      ~finally:(fun () -> try Unix.unlink tmp_dot with _ -> ())
end *)
