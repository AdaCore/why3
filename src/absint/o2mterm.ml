module Make(S:sig type t end) = struct
  module TMap = Map.Make(struct type t = S.t let compare = compare end)
  type t = {
    to_term: unit Term.Mterm.t TMap.t;
    to_t: S.t Term.Mterm.t;
  }

  let empty = { to_term = TMap.empty; to_t = Term.Mterm.empty; }

  let get_all oto t =
    try
      TMap.find t oto.to_term
    with
    | Not_found -> Term.Mterm.empty

  let to_term oto t =
    TMap.find t oto.to_term |> Term.Mterm.choose |> fst

  let to_terms oto t =
    TMap.find t oto.to_term

  let to_t oto te =
    Term.Mterm.find te oto.to_t

  let add oto te t =
    let all = get_all oto t in
    let all = Term.Mterm.add te () all in
    begin
      try
        to_t oto te |> ignore; assert false
      with
      | Not_found -> ()
    end;

    { to_term = TMap.add t all oto.to_term;
      to_t = Term.Mterm.add te t oto.to_t; }

  let remove_t oto t =
    { to_term = TMap.remove t oto.to_term;
      to_t = Term.Mterm.fold_left
          (fun m k () ->
             Term.Mterm.remove k m) oto.to_t (get_all oto t) }

  let remove_term oto te =
    let all = get_all oto (Term.Mterm.find te oto.to_t) in
    let all = Term.Mterm.remove te all in
    { to_term = TMap.add (Term.Mterm.find te oto.to_t) all  oto.to_term;
      to_t = Term.Mterm.remove te oto.to_t }

  let card a = 
    Term.Mterm.cardinal a.to_t

  let card2 a =
    TMap.filter (fun _ k -> k <> Term.Mterm.empty) a.to_term |> TMap.cardinal


  let union f a b =
    let c = a in
    Term.Mterm.fold_left (fun c te t ->
        try
          if not (Term.Mterm.find te c.to_t = t) then
            f (Term.Mterm.find te c.to_t) t;
          c
        with
        | Not_found ->
          add c te t) c b.to_t
end
