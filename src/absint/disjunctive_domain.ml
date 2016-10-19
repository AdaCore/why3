open Domain

module Make(A:DOMAIN) = struct
  type t = A.t list
  type man = A.man
  type env = A.env

  let create_manager = A.create_manager

  let bottom m e = []

  let top m e = [A.top m e]

  let canonicalize m = List.iter (A.canonicalize m)

  let is_bottom man t =
    List.map (A.is_bottom man) t
    |> List.fold_left ( && ) true

  let is_leq man a b =
    (* not correct, we can have a <= b and this function saying no *)
    let one_in_many t =
      List.map (A.is_leq man t) b
      |> List.fold_left ( || ) false
    in
    List.map one_in_many a
    |> List.fold_left (&&) true

  let cleanup man a =
    List.filter (fun t -> not (A.is_bottom man t)) a

  let threshold = 5


  let join_one man = function
    | [] -> None
    | t::q -> Some (List.fold_left (A.join man) t q)

  let unwrap_domain = function
    | None -> []
    | Some t -> [t]

  let cleanup_hard man c =
    let rec zip a = function
      | [] -> a
      | t::q ->
        let p = List.map (A.is_leq man t) (q @ a)
                |> List.fold_left (||) false in
        if p then
          zip a q
        else
          zip (t::a) q
    in
    zip [] c

  let join man a b =
    let a = cleanup man a in
    let b = cleanup man b in
    let a =
      if List.length a > threshold then
        join_one man a |> unwrap_domain
      else a
    in
    let b =
      if List.length b > threshold then
        join_one man b |> unwrap_domain
      else b
    in
    let c = a @ b in
    cleanup_hard man c


  let join_list man t =
    match t with
    | [] -> []
    | [t] -> t
    | t::q ->
      List.fold_left (join man) t q
  
  let print fmt = List.iter (A.print fmt)

  let widening man a b =
    let a = cleanup man a in
    let b = cleanup man b in
    let a =
      join_one man a
    in
    let b =
      join_one man b
    in
    match a, b with
    | None, None -> []
    | None, Some c -> [c]
    | Some c, None -> [c]
    | Some c, Some d ->
        [A.widening man c d]

  let meet_lincons_array man t e  = List.map (fun t -> A.meet_lincons_array man t e) t

  let forget_array man t a b =
    List.map (fun t -> A.forget_array man t a b) t

  let assign_linexpr man t v l t_ =
    (* FIXME: what if t_ <> None? *)
    assert (t_ = None);
    List.map (fun t -> A.assign_linexpr man t v l None) t

  let to_term env pmod man t var_mapping =
    let t = cleanup_hard man t in
    let f = A.to_term env pmod in
    let t = List.map (fun t -> f man t var_mapping) t
    |> Term.t_or_simp_l in
    Pretty.print_term Format.err_formatter t;
    t
end
