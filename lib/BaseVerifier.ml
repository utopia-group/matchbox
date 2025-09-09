open Core
open BaseLogic


module ActionMapper = struct 

    type action = int

    type t = {
        index : int String.Map.t;
        unindex : string Int.Map.t;
        pair : int Int.Map.t Int.Map.t;
        unpair : (int * int) Int.Map.t
    }

    let fresh_idx mapper = 
        let compare = Int.compare in 
        Map.data mapper.index @
        Map.keys mapper.unindex @
        Map.keys mapper.unpair @
        List.bind (Map.data mapper.unpair) ~f:(fun (i,j) -> [i;j])
        |> List.max_elt ~compare
        |> Option.value ~default:0
        |> (+) 1

    let set mapper name idx = 
        {mapper with 
            index = Map.add_exn mapper.index ~key:name ~data:idx;
            unindex = Map.add_exn mapper.unindex ~key:idx ~data:name;
        }

    let get (mapper : t) (name : string) : (t * action) = 
        match Map.find mapper.index name with 
        | None -> 
            let a = fresh_idx mapper in
            (set mapper name a, a)
        | Some a -> 
            (mapper, a)
    
    let _findpair mapper a1 a2 = 
        let lo = Int.min a1 a2 in 
        let hi = Int.max a1 a2 in 
        match Map.find mapper.pair lo with 
        | None -> None
        | Some inner_map -> 
            Map.find inner_map hi

    let _addpair_exn mapper a1 a2 a12 =
        let lo = Int.min a1 a2 in 
        let hi = Int.max a1 a2 in 
        let pair = 
            match Map.find mapper.pair lo with 
            | None -> 
                let data = Int.Map.singleton hi a12 in 
                Map.add_exn mapper.pair ~key:lo ~data
            | Some map ->
                match Map.find map hi with 
                | None -> 
                    let data = Map.add_exn map ~key:hi ~data:a12 in 
                    Map.add_exn mapper.pair ~key:lo ~data
                | Some a12' ->
                    failwithf "tried to add (%d, %d) |=> %d, but had already mapped it to %d"
                        a1 a2 a12 a12' ()
        in
        let unpair = Map.add_exn mapper.unpair ~key:a12 ~data:(a1,a2) in
        { mapper with pair; unpair} 



    let pair mapper (a1 : action) (a2 : action) : t * action = 
        match _findpair mapper a1 a2 with 
        | Some a12 -> mapper, a12
        | None -> 
            let a12 = fresh_idx mapper in 
            _addpair_exn mapper a1 a2 a12, a12

    let to_bv mapper action = 
        SMT.bv action (fresh_idx mapper - 1)

end


let action_fun (f : Symbol.t) = 
    Symbol.to_string f
    |> Printf.sprintf "%s$action"

let data_fun (f : Symbol.t) arg = 
    let table_name = Symbol.to_string f in
    Printf.sprintf "%s$%s" table_name arg

let get_table_schema_clause ctx clause = 
    Type.get_table_exn (BaseChecker.clause_type ctx clause)

let compile_clause (ctx : Type.ctx) (acts : ActionMapper.t) ({defined; definition} : t) : SMT.expr = 
    let typ = get_table_schema_clause ctx definition in 
    let ins_types = Type.get_keys typ in
    let outs_types = Type.get_data typ |> Map.to_alist in
    let xs = List.map ins_types ~f:(fun (x,_) -> SMT.var x) in 
    let ins_sorts = List.map ins_types ~f:(fun (x, w) -> (x, SMT.bv_sort w)) in
    match definition with 
    | Id f ->
        SMT.(and_
            (forall ins_sorts (
                (=) [ apply (action_fun defined) xs;
                      apply (action_fun f) xs]
            ) :: List.map outs_types ~f:(fun (arg, _) ->
                forall ins_sorts (
                    (=)[
                        apply (data_fun defined arg) xs;
                        apply (data_fun f arg) xs
                    ])
            )
            ))
    | Compose (Id f, Id g) -> 
        let fouts = Map.to_alist (Type.get_data (Type.find_table_exn ctx (Symbol.to_string f))) in
        (* by the type system, we know fouts == gins *)
        let fs_of_xs = List.map fouts ~f:(fun (arg, _) ->
            SMT.apply (data_fun f arg) xs;
        ) in
        SMT.(and_ 
            (forall ins_sorts (
                (=) [
                    apply (action_fun defined) xs;
                    apply (action_fun g) fs_of_xs;
                ]
            ) :: List.map outs_types ~f:(fun (arg, _) ->
                forall ins_sorts (
                    (=)[
                        apply (data_fun defined arg) xs;
                        apply (data_fun g arg) fs_of_xs
                    ])
            )))
    | Join (Id f, Id g, _) ->
        let ftype = Type.find_table_exn ctx (Symbol.to_string f) in 
        let gtype = Type.find_table_exn ctx (Symbol.to_string g) in 
        let fins = Type.get_keys ftype |> List.map ~f:(fun (x,_) -> SMT.var x) in
        let fouts = Type.get_data ftype in 
        let gins = Type.get_keys ftype |> List.map ~f:(fun (x,_) -> SMT.var x)  in 
        let gouts = Type.get_data gtype in
        let is_f_arg arg =
            match Map.find fouts arg, Map.find gouts arg with 
            | None, None ->
                failwithf "[verifier] type error. couldn't find output %s in join" arg ()
            | Some _ , Some _ ->
                failwithf "[verifier] type error, found %s in both outputs of join" arg ()
            | Some _, None -> 
                true
            | None, Some _ -> 
                true
        in 
        let factionnames = Type.get_table_actions ctx (Symbol.to_string f) in 
        let gactionnames = Type.get_table_actions ctx (Symbol.to_string g) in
        let actpairs = List.cartesian_product factionnames gactionnames in 
        let action_term = 
            SMT.(forall ins_sorts (
                and_ @@ List.map actpairs ~f:(fun (fname, gname) -> 
                    (* assume we've already analyzed the schema and computed an action mapper *)
                    let _, af = ActionMapper.get acts fname in
                    let _, ag = ActionMapper.get acts gname in 
                    let _, afg = ActionMapper.pair acts af ag in
                    let f_bv = ActionMapper.to_bv acts af in 
                    let g_bv = ActionMapper.to_bv acts ag in 
                    let fg_bv = ActionMapper.to_bv acts afg in 
                    implies [
                        (=) [
                            f_bv;
                            apply (action_fun f) xs
                        ];
                        (=) [
                            g_bv;
                            apply (action_fun g) xs
                        ];
                        (=) [
                            fg_bv;
                            apply (action_fun defined) xs
                        ]
                    ]
                )
            )
            )
        in
        SMT.and_ @@ List.concat [
            [ action_term ];
            List.map outs_types ~f:(fun (arg, _) -> 
                SMT.(forall ins_sorts (
                    (=) [
                        apply (data_fun defined arg) xs;
                        if is_f_arg arg then 
                            apply (data_fun f arg) fins
                        else 
                            apply (data_fun g arg) gins;
                    ]
                ))
            )
        ]
    (* | MapOut f o -> *)

    | _ -> failwith "[verifier] todo"
