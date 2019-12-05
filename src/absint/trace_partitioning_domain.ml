open Domain

module Make(A:DOMAIN) = struct
  type label = Node of int | Star of  int
  type path = label list

  let hash _ _ = assert false
  let is_eq _ _ _ = assert false

  let rec path_height = List.length

  let print_path = List.iter (function
      | Node i -> Format.eprintf "%d@." i;
      | Star i -> Format.eprintf "%d*@." i;
    )

  let rec path_add l p =
    let a = List.find_all (function
        | Node i | Star i when l = i -> true
        | _ -> false) p in
    if List.length a >= 2 then
      begin
      assert (List.length a = 2);
      let rec put_star found = function
        | [] -> []
        | t::q ->
          let found, t =
            if (match t with
                | Node i | Star i when l = i -> true
                | _ -> false)
            then
              not found, Star l
            else
              found, t
          in
          if found then
            put_star found q
          else
            t::(put_star found q)
      in
      (Node l) :: put_star false p
      end
    else
      (Node l)::p

  let rec path_leq p1 p2 =
    match p1, p2 with
    | [], [] -> true
    | (Node t)::q, (Node t')::q' | (Node t)::q, (Star t')::q' ->
      t = t' && (path_leq q q')
    | _ -> false

  exception LNone_found

  let sum_list f a =
    let a = List.sort (fun (_, i) (_, j) ->
        compare i j) a in
    let rec merge = function
      | [] -> []
      | [b] -> [b]
      | (b, a)::(d, c)::q ->
        if a = c then
          merge ((f b d, a)::q)
        else
          (b, a) :: (merge ((d, c)::q))
    in
    merge a

  type t = (A.t * path) list
  type man = A.man
  type env = A.env

  let create_manager = A.create_manager

  let bottom m e = []

  let top m e = [A.top m e, []]

  let canonicalize m = List.iter (fun t -> fst t |> A.canonicalize m)

  let is_bottom man t =
    List.map (fun t -> fst t |> A.is_bottom man) t
    |> List.fold_left (&&) true

  let is_leq man a b =
    let one_in_many (t, path) =
      List.map (fun (t_, path_) ->
          A.is_leq man t t_) b
      |> List.fold_left (||) false
    in
    List.map one_in_many a
    |> List.fold_left (&&) true

  let cleanup man a =
    List.filter (fun (t, _) -> not (A.is_bottom man t)) a

  let threshold = 1000

  let join_one man = function
    | [] -> None
    | (a, b)::q ->
      let qa, qb = List.split q in
      Some (List.fold_left (A.join man) a qa, [])

  let unwrap_domain = function
    | None -> []
    | Some t -> [t]

  let join man a b =
    let a = cleanup man a in
    let b = cleanup man b in
    let c = a @ b in
    sum_list (fun a b -> A.join man a b) c

  let join_list man t =
    match t with
    | [] -> []
    | [t] -> t
    | t::q ->
      List.fold_left (join man) t q

  let print fmt = List.iter (fun (a,_) -> A.print fmt a)

  let widening man a b =
    let a = cleanup man a in
    let b = cleanup man b in
    let c = a @ b in
    sum_list (fun a b -> A.widening man a b) c


  let meet_lincons_array man t e  = List.map (fun (t, p) -> A.meet_lincons_array man t e, p) t

  let forget_array man t a b =
    List.map (fun (t, p) -> A.forget_array man t a b, p) t

  let assign_linexpr man t v l t_ =
    (* FIXME: what if t_ <> None? *)
    assert (t_ = None);
    List.map (fun (t, p) -> A.assign_linexpr man t v l None, p) t

  let to_term env pmod man t var_mapping =
    let t = cleanup man t in
    let f = A.to_term env pmod in
    let t = List.map fst t in
    let t = List.map (fun t -> f man t var_mapping) t
    |> Term.t_or_simp_l in
    t

  let push_label man env i t =
    List.map (fun (d, p) -> A.push_label man env i d,  path_add i p) t |> sum_list (A.join man)

  let to_lincons_array man t =
    match join_one man t with
    | None -> assert false
    | Some t -> A.to_lincons_array man (fst t)

  let get_linexpr man t v =
    match join_one man t with
    | None -> None
    | Some s ->
      A.get_linexpr man (fst s) v

end
