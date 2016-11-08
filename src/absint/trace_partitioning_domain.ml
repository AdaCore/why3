open Domain

module Make(A:DOMAIN) = struct
  type label = int
  type path = 
    | LTree of (path list) * label
    | LNone

  let hash _ _ = assert false
  let is_eq _ _ _ = assert false

  let rec print_path = function
    | LNone -> Format.eprintf "none"
    | LTree(p, i) -> Format.eprintf " %d -> (" i;
      List.iter print_path p;
      Format.eprintf ") "

  let rec path_height = function
    | LNone -> 0
    | LTree(p, i) -> 1 + (List.map path_height p |> List.fold_left max 0)

  let rec path_leq p1 p2 =
    (* FIXME: quadratic and inefficient *)
    match p1 with
    | LNone -> p2 = LNone
    | LTree(p, i) ->
      match p2 with
      | LNone -> true
      | LTree(p2, i2) -> i = i2 && List.fold_left (fun t p1 ->
          t && List.fold_left (fun t p2 ->
              t || path_leq p1 p2) false p2) true p

  exception LNone_found
  
  let sum_list f a =
    let a = List.sort (fun (i, _) (j, _) ->
        compare i j) a in
    let rec merge = function
      | [] -> []
      | [b] -> [b]
      | (a, b)::(c, d)::q ->
        if a = c then
          merge ((a, f b d)::q)
        else
          (a, b) :: (merge ((c, d)::q))
    in
    merge a

  let rec path_join p1 p2 =
    match p1 with
    | LNone -> LNone
    | LTree(p, i) ->
      match p2 with
      | LNone -> LNone
      | LTree(p_, i_) ->
        if i = i_ then
          let p = p @ p_ in
          try
            List.map (function
                | LNone -> raise LNone_found
                | LTree(p, i) -> i, LTree(p, i)) p
            |> sum_list path_join
            |> List.map snd
            |> fun t -> LTree(t, i)
          with
          | LNone_found -> LNone
        else
          LNone

  let rec path_score p1 p2 =
    match p1 with
    | LNone -> if p2 = LNone then 1 else 0
    | LTree(p, i) ->
      match p2 with
      | LNone -> 0
      | LTree(p_, i_) ->
        if i = i_ then
          1 + begin
          let p = p @ p_ in
          try
            List.map (function
                | LNone -> raise LNone_found
                | LTree(p, i) -> i, (LTree(p, i), 1)) p
            |> sum_list (fun (p, c) (p_, c2) ->
                (p, (max c c2 +
                path_score p p_)))
            |> List.map (fun (_, (_, c)) -> c)
            |> List.fold_left max 0
          with
          | LNone_found -> 0
          end
        else
          0
          

  let rec path_truncate tr p =
    if tr = 0 then LNone
    else match p with
      | LNone -> LNone
      | LTree(p, i) ->
        let tr =  if List.length p >= 2 then tr - 1 else tr
        in
        LTree(List.map (path_truncate tr) p, i)

  let threshold_path = 4

  let rec path_widen p1 p2 =
    match p1 with
    | LNone -> LNone
    | LTree(p, i) ->
      match p2 with
      | LNone -> LNone
      | LTree(p_, i_) ->
        if i = i_ then
          let p = p @ p_ in
          try
            List.map (function
                | LNone -> raise LNone_found
                | LTree(p, i) -> i, (LTree(p, i), false)) p
            |> sum_list (fun (a,b) (c, d) -> path_widen a c, true)
            |> List.map (fun ((_, (_, t)) as a) -> if not t then  raise LNone_found else a)
            |> List.map snd
            |> List.map fst
            |> fun t -> LTree(t, i)
          with
          | LNone_found -> LNone
        else
          LNone

  type t = (A.t * path) list
  type man = A.man
  type env = A.env

  let create_manager = A.create_manager

  let bottom m e = []

  let top m e = [A.top m e, LNone]

  let canonicalize m = List.iter (fun t -> fst t |> A.canonicalize m)

  let is_bottom man t =
    List.map (fun t -> fst t |> A.is_bottom man) t
    |> List.fold_left (&&) true

  let is_leq man a b =
    let one_in_many (t, path) =
      List.map (fun (t_, path_) ->
          path_leq path path_ && A.is_leq man t t_) b
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
      Some (List.fold_left (A.join man) a qa, List.fold_left path_join b qb)

  let unwrap_domain = function
    | None -> []
    | Some t -> [t]

  let cleanup_hard man c =
    let rec zip c = function
      | [] -> c
      | (a, b)::q ->
        let p = List.map (fun (a_, b_) -> path_leq b b_ && A.is_leq man a a_) (q @ c)
                |> List.fold_left (||) false in
        let c, f = List.fold_left (fun (myc, f) (td, tp) ->
            if not f && A.is_leq man td a && A.is_leq man a td then
              (a, path_join tp b)::myc, true
            else
              (td, tp)::myc, f
          ) ([], false) c in
        if p || f then
          zip c q
        else
          zip ((a, b)::c) q
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
  
  let print fmt = List.iter (fun (a,_) -> A.print fmt a)

  let widening man a b =
    let measure (d, p) (score, best) ((d_, p_) as a)  =
      let new_score = path_score p p_ in
      if score <= new_score then
        new_score, a
      else
        score, best
    in
    let a = cleanup man a in
    let b = cleanup man b in
    let a = List.fold_left (fun a t ->
        let score, best = List.fold_left (measure t) (-1, t) a in

        let bh = path_height (snd best) in
        let th = path_height (snd t) in
        let pth = path_widen (snd t) (snd best) in
        let r = if path_height pth < min bh th then A.join man (fst best) (fst t) else A.widening man (fst best) (A.join man (fst best) (fst t))
        in

        let replacement = r, pth in
        if score = -1 then
          [t]
        else
          List.map (fun t -> if t == best then replacement else t) a
      ) a b in
    a

  let meet_lincons_array man t e  = List.map (fun (t, p) -> A.meet_lincons_array man t e, p) t

  let forget_array man t a b =
    List.map (fun (t, p) -> A.forget_array man t a b, p) t

  let assign_linexpr man t v l t_ =
    (* FIXME: what if t_ <> None? *)
    assert (t_ = None);
    List.map (fun (t, p) -> A.assign_linexpr man t v l None, p) t

  let to_term env pmod man t var_mapping =
    let t = cleanup_hard man t in
    let f = A.to_term env pmod in
    let t = List.map fst t in
    let t = List.map (fun t -> f man t var_mapping) t
    |> Term.t_or_simp_l in
    Pretty.print_term Format.err_formatter t;
    t

  let push_label man env i t = List.map (fun (d, p) -> A.push_label man env i d, LTree([p], i)) t
  
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
