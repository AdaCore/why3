open Domain

type 'a a = { t: 'a list; c: bool; i: int; }

module Make(A:DOMAIN) = struct

  type t = A.t a
  type env = A.env
  
  let hash man t =
    List.map (A.hash (fst man)) t.t |>
    List.fold_left (+) 0
  
  let is_eq _ _ _ = assert false

  module Hashdom = Hashtbl.Make(struct
      type t = (A.t * A.t * A.man)
      let hash (t, t', man) = A.hash man t + A.hash man t'
      let equal (t, t', man) (t2, t2', _) =
        (A.is_eq man t t2 && A.is_eq man t' t2') ||
        (A.is_eq man t' t2 && A.is_eq man t t2')
    end)
  
  module Hashdoml = Hashtbl.Make(struct
      type t = (A.t * Apron.Lincons1.earray * A.man)
      let hash (t, t', man) = A.hash man t + Hashtbl.hash t'
      let equal (t, t', man) (t2, t2', _) =
        A.is_eq man t t2 && (
          t' = t2')
    end)
  
  
  type disj_man = { join_tbl: bool Hashdom.t; real_join_tbl: A.t Hashdom.t; meet_lincons: A.t Hashdoml.t }
  type man = A.man * disj_man

  let create_manager () = A.create_manager (), { join_tbl = Hashdom.create 1024; real_join_tbl = Hashdom.create 1024; meet_lincons = Hashdoml.create 1024; }

  let bottom m e = { i = 0; t = []; c = true; }

  let top man e = { i = 0; t = [A.top (fst man) e]; c = true; }

  let canonicalize m a = List.iter (A.canonicalize (fst m)) a.t
  
  let print fmt e = List.iter (fun b ->
      A.print fmt b;
      Format.fprintf fmt "@.";) e.t

  let is_bottom man t =
    let man = fst man in
    List.map (A.is_bottom man) t.t
    |> List.fold_left ( && ) true
  
  let a_meet_lincons_array man a l =
    (*try
      Hashdoml.find (snd man).meet_lincons (a, l, fst man)
    with
    | Not_found ->*)
      let c = A.meet_lincons_array (fst man) a l in
      (* Hashdoml.add (snd man).meet_lincons (a, l, fst man) c; *)
      c

  let a_is_leq man a b =
    A.is_leq (fst man) a b
  
  let a_join man a b =
    (*try
      Hashdom.find (snd man).real_join_tbl (a, b, fst man)
    with
    | Not_found ->*)
      let c = A.join (fst man) a b in
      (* Hashdom.add (snd man).real_join_tbl (a, b, fst man) c; *)
      c

  let is_leq man a b =
    let rec aux = function
      | [] -> true
      | t::q ->
        (* not correct, we can have a <= b and this function saying no *)
        let rec one_in_many = function
          | [] -> false
          | t':: q' ->
            a_is_leq man t t' || one_in_many q'
        in
        one_in_many b.t && aux q
    in
    aux a.t

  let cleanup man a =
    let man = fst man in
    if a.c then a
    else
      { t = List.filter (fun t -> not (A.is_bottom man t)) a.t; c = true; i = a.i; }

  let threshold = 25

  let join_one man { t; i; _ } =
    match t with
    | [] -> bottom () ()
    | t::q -> { t = [List.fold_left (a_join man) t q]; c = true; i; }

  let join_precise man a b =
    { t = List.fold_left (fun a t ->
        let find_precise_join e =
          A.is_join_precise (fst man) t e
        in
        let a, found = List.fold_left (fun (a, found) e ->
            match find_precise_join e with
            | None -> e::a, found
            | Some c -> c::a, true
          ) ([], false) a in
        if found then
          a
        else
          t::a
        ) a.t b.t; c = false; i = 0; }

  let cleanup_hard man { t = c; i; _ } =
    let rec zip a = function
      | [] -> a
      | t::q ->
        let p = List.map (a_is_leq man t) (q @ a)
                |> List.fold_left (||) false in
        if p then
          zip a q
        else
          zip (t::a) q
    in
    { t = zip [] c; c = true; i } |> join_precise man (bottom () ())
    |> fun a -> { a with c = true; }


  let join man a b =
    let a = cleanup man a in
    let b = cleanup man b in
    let i = (max a.i b.i) + 1 in
    if i > 0 then
      let a =
        if List.length a.t > threshold then
          join_one man a
        else a
      in
      let b =
        if List.length b.t > threshold then
          join_one man b
        else b
      in
      let c = { t = a.t @ b.t; i; c = false; } in
      let c = cleanup_hard man c in
      { c with i = 0; }
    else
      { t = a.t @ b.t; i; c = false; }




  let join_list man t =
    match t with
    | [] -> bottom () ()
    | [t] -> t
    | t::q ->
      List.fold_left (join man) t q
  
  let is_join_precise man a b = Some (join man a b)
  

  (* used once by loop, so it can be costly *)
  let widening man a b =
    let a = cleanup_hard man a in
    let b = cleanup_hard man b in
    let a =
      if List.length a.t > threshold then
        join_one man a
      else a
    in
    let b =
      if List.length b.t > threshold then
        join_one man b
      else b
    in
    let b_leq = List.map (fun b ->
        b, try
          List.find (fun a ->
              a_is_leq man a b) a.t
        with
        | Not_found -> b
      ) b.t
    in
    let c = {t = List.map (fun (k, v) ->
         A.widening (fst man) v k) b_leq; c = false; i = 0; } |> cleanup man in
    c

  let meet_lincons_array man t e  =
    { t with t = List.map (fun t -> a_meet_lincons_array man t e) t.t; c = false; }

  let forget_array man t a b =
    { t with  t = List.map (fun t -> A.forget_array (fst man) t a b) t.t; c = false; }

  let assign_linexpr man t v l t_ =
    (* FIXME: what if t_ <> None? *)
    assert (t_ = None);
    { t with t = List.map (fun t -> A.assign_linexpr (fst man) t v l None) t.t; c = false; }

  let to_term env pmod man t var_mapping =
    let f = A.to_term env pmod (fst man) in
    let t = cleanup_hard man t in
    let globals =
      match (join_one man t).t with
      | [] -> []
      | [t] ->
        f t var_mapping |> Ai_logic.extract_atom_from_conjuction []
      | _ -> assert false
    in
    let rec redundant t =
      if List.exists (Term.t_equal t) globals then
        Term.t_true
      else
        Term.t_map_simp redundant t
    in
    let t = List.map (fun t ->
        f t var_mapping
        |> redundant) t.t
    |> Term.t_or_simp_l in
    List.fold_left Term.t_and_simp t globals

  let push_label man env i t = t

  let to_lincons_array man t =
    match (join_one man t).t with
    | [] -> assert false
    | [t] -> A.to_lincons_array (fst man) t
    | _ -> assert false

  let get_linexpr man t v =
    match (join_one man t).t with
    | [] -> None
    | [s] ->
      A.get_linexpr (fst man) s v
    | _ -> assert false

end
