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


  let join man a b =
    let a = List.filter (fun t -> not (A.is_bottom man t)) a in
    let b = List.filter (fun t -> not (A.is_bottom man t)) b in
    let a =
      if List.length a > 6 then
        [List.fold_left (A.join man) (List.hd a) (List.tl a)]
      else a
    in
    let b =
      if List.length b > 6 then
        [List.fold_left (A.join man) (List.hd b) (List.tl b)]
      else b
    in
    let c = a @ b in
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
    match c with
    | [] -> []
    | t::q -> zip [t] q


  let join_list man t =
    List.map (List.filter (fun t -> not (A.is_bottom man t))) t
    |> List.concat
  
  let print fmt = List.iter (A.print fmt)

  let widening man a b =
    let a = List.filter (fun t -> not (A.is_bottom man t)) a in
    let b = List.filter (fun t -> not (A.is_bottom man t)) b in
    let a =
      if List.length a > 6 then
        [List.fold_left (A.widening man) (List.hd a) (List.tl a)]
      else a
    in
    let b =
      if List.length b > 6 then
        [List.fold_left (A.widening man) (List.hd b) (List.tl b)]
      else b
    in
    join man a b

  let meet_lincons_array man t e  = List.map (fun t -> A.meet_lincons_array man t e) t

  let forget_array man t a b =
    List.map (fun t -> A.forget_array man t a b) t

  let assign_linexpr man t v l t_ =
    (* FIXME: what if t_ <> None? *)
    assert (t_ = None);
    List.map (fun t -> A.assign_linexpr man t v l None) t

  let to_term env pmod man t var_mapping =
    let f = A.to_term env pmod in
    let t = List.map (fun t -> f man t var_mapping) t
    |> Term.t_or_simp_l in
    Pretty.print_term Format.err_formatter t;
    t
end
