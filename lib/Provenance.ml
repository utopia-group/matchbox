open Core
type ('a, 'b) t = ('a * 'b) list

let image (p : ('a, 'b) t) (s : 'a) ~equal = 
  List.bind p ~f:(fun (s', t) -> 
    if equal s s' then 
      [t]
    else 
      []
  )

let image' p ss ~equal =
  List.bind ss ~f:(image p ~equal)

let preimage (p : ('a, 'b) t) (t : 'b) ~equal =
  List.bind p ~f:(fun (s, t') -> 
    if equal t t' then 
      [s]  
    else 
      []
  )

let preimage' p tt ~equal =
  List.bind tt ~f:(image p ~equal)

let insert (p : ('a, 'b) t) (s : 'a) (ts : 'b list) : ('a, 'b) t=
  let p_to_add = List.map ts ~f:(fun t -> (s, t)) in 
  p @ p_to_add

let _unsafe_delete (p : ('a,'b) t) (s : 'a) ~equal : ('a,'b) t= 
  List.filter p ~f:(fun (s',_) -> not (equal s s'))

let delete (p : ('a, 'b) t) (s : 'a) ~(sequal:'a -> 'a -> bool) ~(tequal : 'b -> 'b -> bool) : ('a,'b) t * 'b list =
  let candidates : 'b list = image p s ~equal:sequal in 
  let p' = _unsafe_delete p s ~equal:sequal in 
  let to_delete = List.filter candidates ~f:(fun t ->
      not (List.is_empty (preimage p' t ~equal:tequal))
    )
  in 
  p', to_delete