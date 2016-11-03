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

  let union a b =
    let c = a in
    Term.Mterm.fold_left (fun c te t ->
        try
          assert (Term.Mterm.find te c.to_t = t); c
        with
        | Not_found ->
          add c te t) c b.to_t

  let card a = 
    Term.Mterm.cardinal a.to_t

  let choose a =
    Term.Mterm.choose a.to_t

end
