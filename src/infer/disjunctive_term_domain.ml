open Domain

type 'a a = { t: 'a list; c: bool; i: int; }


module Make(S:sig
    module A:TERM_DOMAIN
    val env: Env.env
    val th_known: Decl.known_map
    val mod_known: Pdecl.known_map
  end) = struct
  module A = S.A

  open Ai_logic
  module Ai_logic = Ai_logic.Make(struct
      let env = S.env
      let th_known = S.th_known
      let mod_known = S.mod_known
    end)

  type t = A.t a
  type env = A.env

  let is_eq _ _ _ = assert false

  type disj_man = ()
  type man = A.man * disj_man

  let (create_manager:unit -> man) = fun () -> A.create_manager (), ()

  let bottom _ _ = { i = 0; t = []; c = true; }

  let top man e = { i = 0; t = [A.top (fst man) e]; c = true; }

  let canonicalize m a = List.iter (A.canonicalize (fst m)) a.t

  let print fmt e = List.iter (fun b ->
      A.print fmt b;
      Format.fprintf fmt "@.";) e.t

  let is_bottom man t =
    let man = fst man in
    List.map (A.is_bottom man) t.t
    |> List.fold_left ( && ) true

  let is_leq (man, _) a b =
    let rec aux = function
      | [] -> true
      | t::q ->
        (* not correct, we can have a <= b and this function saying no *)
        let rec one_in_many = function
          | [] -> false
          | t':: q' ->
            A.is_leq man t t' || one_in_many q'
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

  let join_one (man, _) { t; i; _ } =
    match t with
    | [] -> bottom () ()
    | t::q -> { t = [List.fold_left (A.join man) t q]; c = true; i; }

  let join_precise man a b =
    { t = List.fold_left (fun a t ->
        let find_precise_join e =
          A.is_join_precise man t e
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

  let cleanup_hard (man, _) { t = c; i; _ } =
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
              A.is_leq (fst man) a b) a.t
        with
        | Not_found -> b
      ) b.t
    in
    let c = {t = List.map (fun (k, v) ->
         A.widening (fst man) v k) b_leq; c = false; i = 0; } |> cleanup man in
    c

  let to_term man t =
    let f = A.to_term (fst man) in
    let t = cleanup_hard man t in
    let globals =
      match (join_one man t).t with
      | [] -> []
      | [t] ->
        f t |> extract_atom_from_conjuction []
      | _ -> assert false
    in
    let rec redundant t =
      if List.exists (Term.t_equal t) globals then
        Term.t_true
      else
        Term.t_map_simp redundant t
    in
    let t = List.map (fun t ->
        f t
        |> redundant) t.t
    |> Term.t_or_simp_l in
    List.fold_left Term.t_and_simp t globals

  let push_label _ _ _ t = t

  let make_consistent _ = failwith "not implemented"

  let add_lvariable_to_env (man, _) = A.add_lvariable_to_env man
  let add_variable_to_env (man, _) = A.add_variable_to_env man

  let forget_region (man, _) a b d =
    { d with t = List.map (A.forget_region man a b) d.t }

  let forget_var (man, _) v d =
    { d with t = List.map (A.forget_var man v) d.t }

  let forget_term (man, _) v d =
    { d with t = List.map (A.forget_term man v) d.t }

  let rec meet_term man term elt =
    let open Term in
    match term.t_node with
    | Tbinop (Tor, a, b) ->
      join man (meet_term man a elt) (meet_term man b elt)
    | Tbinop (Tand, a, b) ->
      meet_term man a elt |> meet_term man b
    | Tbinop _ -> assert false
    | _ -> {elt with t = List.map (A.meet_term (fst man) term) elt.t }

end
