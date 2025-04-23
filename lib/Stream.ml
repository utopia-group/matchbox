open Core

type 'a t = 
  | Nil
  | Cons of 'a * ('a t lazy_t)

let is_empty = function 
  | Nil -> true
  | Cons _ -> false

let rec create ?(nilif=fun _-> false) init ~f = 
  if nilif init then
    Nil
  else
    Cons (init, lazy (create (f init) ~f ~nilif))

let nats = create 0 ~f:((+) 1)

let empty = function 
  | Nil -> true
  | _ -> false

let singleton x = Cons (x, lazy Nil)
let return = singleton

let get = function 
  | Cons(init,_) -> init
  | Nil -> failwith "[get error] stream terminated"

let next = function
  | Cons(x, xs) -> (x, Lazy.force xs)
  | Nil -> failwith "[next error] stream terminated"


let rec of_list xs = 
  match xs with 
  | [] -> Nil
  | x::xs -> 
    Cons (x, lazy (of_list xs))

let rec map_list xs ~f =
  match xs with 
  | [] -> Nil
  | x::xs -> 
    Cons (f x, lazy (map_list xs ~f))

let rec map xs ~f =
  match xs with 
  | Nil -> Nil
  | Cons(x, xs) -> 
    Cons (f x, lazy (map (Lazy.force xs) ~f))


let rec find xs ~f = 
  match xs with 
  | Nil -> None
  | Cons (x, _) when f x -> Some x
  | Cons (_, xs) -> 
    find (Lazy.force xs) ~f

let rec find_map xs ~f = 
  match xs with 
  | Nil -> None
  | Cons (x, xs) -> begin
    match f x with 
    | None -> find_map (Lazy.force xs) ~f
    | Some o -> Some o
  end

let member x xs ~equal = 
    find xs ~f:(equal x)
    |> Option.is_some

let rec filter_map xs ~f = 
  match xs with 
  | Nil -> Nil
  | Cons (x, xs) -> 
    match f x with 
    | None -> Lazy.force xs |> filter_map ~f
    | Some y -> 
      Cons (y, lazy (filter_map (Lazy.force xs) ~f))

let filter xs ~f = 
  filter_map xs ~f:(fun x -> if f x then Some x else None)

let rec concat s1 s2 = 
  match s1 with 
  | Nil -> Lazy.force s2
  | Cons (x, xs) -> 
    Cons (x, lazy (concat (Lazy.force xs) s2))

let (@) = concat

let rec concat_lazy s1 s2 = 
  match s1 with 
  | Nil -> Lazy.force s2
  | Cons (x, xs) -> 
    Cons (x, lazy (concat_lazy (Lazy.force xs) s2))

let (++) = concat_lazy

let rec dovetail s1 s2 : 'a t = 
  match Lazy.force s1 with 
  | Nil -> Lazy.force s2
  | Cons (x,s1') -> 
    Cons (x, lazy (dovetail s2 s1'))

let rec bind xs ~f = 
  match xs with 
  | Nil -> Nil
  | Cons (x, xs) -> 
    (f x) @ lazy (bind (Lazy.force xs) ~f)

let rec dovebind xs ~f = 
  match xs with 
  | Nil -> Nil 
  | Cons (x, xs) -> 
    (f x) ++ lazy (dovebind  (Lazy.force xs) ~f)

let take i s = 
  let rec loop i s taken = 
    if i = 0 then 
      taken
    else
      match s with 
      | Nil -> taken
      | Cons (x, xs) ->
        loop (i-1) (Lazy.force xs) (x::taken)
  in
  loop i s []
  |> List.rev

let take_cycle i s =
  let rec loop i s' = 
    if i = 0 then 
      []
    else 
      match s' with 
      | Nil -> loop i s
      | Cons (x, xs) -> 
        x :: (Lazy.force xs |> loop (i-1))
  in
  match s with 
  | Nil -> failwith "Cycling an empty stream is infinite"
  | Cons _ -> 
    loop i s
    
    


let nth n s = take (n + 1) s |> List.rev |> List.hd_exn

let nth_mod n s = take (n + 1) s |> List.rev |> List.hd_exn

let prod (s1 : 'a t) (s2 : 'b t) : ('a * 'b) t =
  bind s1 ~f:(fun x -> 
    map s2 ~f:(fun y -> 
      (x,y)
    )
  )

let count_to ~n = create 0 ~f:((+) 1) ~nilif:((=) (n+1))

let ( !<= ) n = count_to ~n

let doveprod s1 s2 = 
  let pair n i = (nth_mod i s1, nth_mod (n - i) s2) in 
  let rec loop n = 
    map (count_to ~n) ~f:(pair n)
    ++ lazy (loop (n+1))
  in
  loop 0  

let rec ndoveprod ss = 
  match ss with 
  | [] -> Cons ([], lazy Nil)
  | s::ss -> 
    ndoveprod ss
    |> prod s
    |> map ~f:(fun (x, ys) -> x :: ys)


let rec nprod (ss : 'a t list) : ('a list) t = 
  match ss with 
  | [] -> Cons([], lazy Nil)
  | s::ss ->
    nprod ss
    |> prod s
    |> map ~f:(fun (x, ys) -> x::ys)
  

let take_and_print s n ~to_string = 
  take n s
  |> List.iteri ~f:(fun i x -> 
    Printf.printf "\n(%d)-------------------\n%s\n-------------------\n%!" i (to_string x);
  )

let iter ~f =
  let rec loop = function
  | Nil -> ()
  | Cons (x, xs) -> f x; force xs |> loop
  in
  loop 


let ( >>= ) s f = bind s ~f
let ( let* ) = (>>=)
let ( let+ ) s f = map s ~f

let liftS2 f s1 s2 = 
  let* x = s1 in
  let+ y = s2 in 
  f x y

let liftS3 f s1 s2 s3 =
  let* f = liftS2 f s1 s2 in 
  let+ x = s3 in 
  f x