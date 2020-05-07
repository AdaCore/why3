open Domain


module Make(TDom : TERM_DOMAIN) = struct

  (* abs_values = abstract values *)
  type t = { abs_values: TDom.t list; c: bool; i: int; }

  type env = TDom.env

  (* let is_eq _ _ _ = assert false *)

  type disj_man = unit
  type man = TDom.man * disj_man

  let (create_manager:unit -> man) = fun _ -> TDom.create_manager (), ()

  let bottom _ _ = { i = 0; abs_values = []; c = true; }

  let top man e = { i = 0; abs_values = [TDom.top (fst man) e]; c = true; }

  let canonicalize m a = List.iter (TDom.canonicalize (fst m)) a.abs_values

  let print fmt e = List.iter (fun b ->
      TDom.print fmt b) e.abs_values

  let is_bottom man t =
    let man = fst man in
    List.fold_left ( && ) true (List.map (TDom.is_bottom man) t.abs_values)

  let is_leq (man, _) a b =
    let rec aux = function
      | [] -> true
      | t::q ->
        (* not correct, we can have a <= b and this function saying no *)
        let rec one_in_many = function
          | [] -> false
          | t':: q' ->
             TDom.is_leq man t t' || one_in_many q' in
        one_in_many b.abs_values && aux q in
    aux a.abs_values

  let cleanup man a =
    let man = fst man in
    let not_bottom t = not (TDom.is_bottom man t) in
    if a.c then a
    else { a with abs_values = List.filter not_bottom a.abs_values; c = true }

  let threshold = 25

  let join_one (man, _) { abs_values; i; _ } =
    match abs_values with
    | [] -> bottom () ()
    | t::q -> { abs_values = [List.fold_left (TDom.join man) t q]; c = true; i; }

  let join_precise man a b =
    let aux a t =
      let find_precise_join e = TDom.is_join_precise man t e in
      let find (a,found) e =
        match find_precise_join e with
        | None -> e :: a, found
        | Some c -> c :: a, true in
      let a, found = List.fold_left find ([], false) a in
      if found then a else t :: a in
    let abs_values = List.fold_left aux a.abs_values b.abs_values in
    { abs_values ; c = false; i = 0; }

  let cleanup_hard (man, _) { abs_values = c; i; _ } =
    let rec zip a = function
      | [] -> a
      | t :: q ->
         let x = List.map (TDom.is_leq man t) (q @ a) in
         let p = List.fold_left (||) false x in
         if p then zip a q else zip (t::a) q in
    let t = { abs_values = zip [] c; c = true; i } in
    let t = join_precise man (bottom () ()) t in
    { t with c = true; }

  let join man a b =
    let a = cleanup man a in
    let b = cleanup man b in
    let i = (max a.i b.i) + 1 in
    if i > 0 then
      let a = if List.length a.abs_values > threshold then join_one man a else a in
      let b = if List.length b.abs_values > threshold then join_one man b else b in
      let c = { abs_values = a.abs_values @ b.abs_values; i; c = false; } in
      let c = cleanup_hard man c in
      { c with i = 0; }
    else
      { abs_values = a.abs_values @ b.abs_values; i; c = false; }

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
    let a = if List.length a.abs_values > threshold then join_one man a else a in
    let b = if List.length b.abs_values > threshold then join_one man b else b in
    let b_leq = List.map (fun b ->
        b,
        try List.find (fun a -> TDom.is_leq (fst man) a b) a.abs_values
        with | Not_found -> b
      ) b.abs_values
    in
    let abs_values = List.map (fun (k, v) -> TDom.widening (fst man) v k) b_leq in
    cleanup man {abs_values; c = false; i = 0; }

  let rec extract_atom_from_conjuction l t =
    let open Term in
    match t.t_node with
    | Tbinop (Tand, a, b) ->
       extract_atom_from_conjuction
         (extract_atom_from_conjuction l a) b
    | _ -> t::l

  let to_term man t =
    let f = TDom.to_term (fst man) in
    let t = cleanup_hard man t in
    let globals = match (join_one man t).abs_values with
      | [] -> []
      | [t] -> extract_atom_from_conjuction [] (f t)
      | _ -> assert false
    in
    let rec redundant t =
      if List.exists (Term.t_equal t) globals then Term.t_true
      else Term.t_map_simp redundant t
    in
    let t = Term.t_or_simp_l (List.map (fun t -> redundant (f t)) t.abs_values) in
    List.fold_left Term.t_and_simp t globals

  let push_label _ _ _ t = t

  let make_consistent _ = failwith "not implemented"

  let add_lvariable_to_env (man, _) = TDom.add_lvariable_to_env man
  let add_variable_to_env (man, _) = TDom.add_variable_to_env man

  let forget_region (man, _) a b d =
    { d with abs_values = List.map (TDom.forget_region man a b) d.abs_values }

  let forget_var (man, _) v d =
    { d with abs_values = List.map (TDom.forget_var man v) d.abs_values }

  let forget_term (man, _) v d =
    { d with abs_values = List.map (TDom.forget_term man v) d.abs_values }

  let rec meet_term man term elt =
    let open Term in
    match term.t_node with
    | Tbinop (Tor, a, b) ->
       join man (meet_term man a elt) (meet_term man b elt)
    | Tbinop (Tand, a, b) -> meet_term man b (meet_term man a elt)
    | Tbinop _ -> assert false
    | _ ->
       let meet = TDom.meet_term (fst man) term in
       let abs_values = List.map meet elt.abs_values  in
       {elt with abs_values }

end
