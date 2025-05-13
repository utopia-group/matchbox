open Core
module Make ( Elt : sig
  type t
  val prio : t -> int (* higher prio is dequeued earlier *)
end) = struct

  type t = Elt.t list

  let pop queue = 
    match queue with 
    | [] -> None
    | elt :: queue' -> Some (elt, queue')

  let rec add (queue : t) (elt : Elt.t) : t = 
    match queue with 
    | [] -> [elt]
    | elt' :: queue' ->
      if Elt.(prio elt > prio elt') then 
        elt :: queue
      else 
        elt' :: add queue' elt

  let add_all (elts : Elt.t list) (queue : t) =
    List.fold elts ~init:queue ~f:add          

end