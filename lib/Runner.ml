open Core

type t  = string

let init (filepath: string) : string = filepath

let run (filepath : t) (str : string) : string =
  Printf.printf "Running %s on \n%s\n%!" filepath str;
  let str = Printf.sprintf "%s\n(exit)\n%!" str in
  let in_chan, out_chan = Core_unix.open_process (Printf.sprintf "%s" filepath) in
  Out_channel.fprintf out_chan "%s\n%!" str; Out_channel.flush out_chan;
  let strs = In_channel.input_lines in_chan in
  Core_unix.close_process (in_chan, out_chan) |> ignore;
  String.concat strs ~sep:"\n"