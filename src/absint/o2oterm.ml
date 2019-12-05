module Make(S:sig type t end) = struct
  module TMap = Map.Make(struct type t = S.t let compare = compare end)
  type t = {
    to_term: Term.term TMap.t;
    to_t: S.t Term.Mterm.t;
  }

  let empty = { to_term = TMap.empty; to_t = Term.Mterm.empty; }


  let add oto te t =
    { to_term = TMap.add t te oto.to_term;
      to_t = Term.Mterm.add te t oto.to_t; }

  let to_term oto t =
    TMap.find t oto.to_term

  let to_t oto te =
    Term.Mterm.find te oto.to_t

  let remove_t oto t =
    { to_term = TMap.remove t oto.to_term;
      to_t = Term.Mterm.remove (TMap.find t oto.to_term) oto.to_t }

  let remove_term oto te =
    { to_term = TMap.remove (Term.Mterm.find te oto.to_t) oto.to_term;
      to_t = Term.Mterm.remove te oto.to_t }

  let union a b f g =
    Term.Mterm.fold_left (fun a te t ->
        let a =
          try
            let t' = to_t a te in
            if t' <> t then
              f t' t te;
            remove_term a te
          with
          | Not_found -> a
        in
        let a =
          try
            let te' = to_term a t in
            if not (Term.t_equal te te') then
              g te' te t;
            remove_t a t
          with
          | Not_found -> a
        in
        add a te t) a b.to_t

  let card a =
    Term.Mterm.cardinal a.to_t

  let choose a =
    Term.Mterm.choose a.to_t

end
