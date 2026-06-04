open Core
let rec space n =
  if n <= 0 then
    ""
  else
    Printf.sprintf " %s" (space (n-1))
