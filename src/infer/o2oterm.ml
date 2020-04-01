open Term

module Make(S:sig type t end) = struct

  module TMap = Map.Make(struct
    type t = S.t
    let compare = compare
  end)

  type t = {
    to_term: term TMap.t;
    to_t: S.t Mterm.t;
  }

  let empty = { to_term = TMap.empty;
                to_t = Mterm.empty; }

  let add oto te t =
    { to_term = TMap.add t te oto.to_term;
      to_t = Mterm.add te t oto.to_t; }

  let to_term oto t =
    TMap.find t oto.to_term

  let to_t oto te =
    Mterm.find te oto.to_t

  let remove_t oto t =
    { to_term = TMap.remove t oto.to_term;
      to_t = Mterm.remove (TMap.find t oto.to_term) oto.to_t }

  let remove_term oto te =
    { to_term = TMap.remove (Mterm.find te oto.to_t) oto.to_term;
      to_t = Mterm.remove te oto.to_t }

  let union oto1 oto2 f g =
    Mterm.fold_left (fun oto te t ->
        let a =
          try
            let t' = to_t oto te in
            if t' <> t then f t' t te;
            remove_term oto te
          with Not_found -> oto in
        let a =
          try
            let te' = to_term a t in
            if not (t_equal te te') then g te' te t;
            remove_t a t
          with Not_found -> a in
        add a te t) oto1 oto2.to_t
    (* TODO replace with the following?
     * let aux term t1 t2 oto = match t1, t2 with
     *   | None, Some t | Some t, None -> add oto term t
     *   | Some t1, Some t2 -> ???
     *   | None, None -> assert false
     * in
     * Mterm.fold2_union aux oto1.to_t oto2.to_t empty *)


  let card a =
    Mterm.cardinal a.to_t

  let choose a =
    Mterm.choose a.to_t

end
