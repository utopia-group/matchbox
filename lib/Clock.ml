open Core

type t = Time.t

let start () = 
  Time.now ()

let stop (c : Time.t) : float =
  Time.(diff (now()) c)
  |> Time.Span.to_ms

