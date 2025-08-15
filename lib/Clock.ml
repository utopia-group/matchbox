open Core

type t = Time_float.t

let start () = 
  Time_float.now ()

let stop (c : Time_float.t) : float =
  Time_float.(diff (now()) c)
  |> Time_float.Span.to_ms

