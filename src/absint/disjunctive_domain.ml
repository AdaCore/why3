open Domain

module Make(A:DOMAIN) = struct
  type t = A.t list
  type man = A.man
  type env = A.env

  let create_manager = A.create_manager

  let bottom m e = []

  let top m e = [A.top m e]

  let canonicalize m _ = () (*List.iter (A.canonicalize m)*)
  
  let print fmt = List.iter (A.print fmt)

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

  let threshold = 25


  let join_one man = function
    | [] -> None
    | t::q -> Some (List.fold_left (A.join man) t q)

  let unwrap_domain = function
    | None -> []
    | Some t -> [t]

  let join_is_precise man a b c =
    let open Apron in
    let linexpr_a = A.to_lincons_array man a in
    let linexpr_b = A.to_lincons_array man b in
    let a, b, linexpr_a =
      if Lincons1.array_length linexpr_a > Lincons1.array_length linexpr_b then
        b, a, linexpr_b
      else
        a, b, linexpr_a
    in
    let precise = ref true in
    for i = 0 to Lincons1.array_length linexpr_a - 1 do
      let line = Lincons1.array_get linexpr_a i in
      (* FIXME: sat lincons *)
      let opp_typ =
        let typ = Lincons1.get_typ line in
        if typ = Lincons1.EQ then
          [Lincons1.SUP, 1; Lincons1.SUP, -1]
        else if typ = Lincons1.SUP then
          [Lincons1.SUPEQ, -1]
        else if typ = Lincons1.SUPEQ then
          [Lincons1.SUP, -1]
        else assert false
      in
      precise := !precise && begin
          List.fold_left (fun p (ty, new_coeff) ->
              let cp = Lincons1.copy line in
              let cst = Lincons1.get_cst cp in
              let cst =
                if new_coeff = -1 then
                  Coeff.neg cst
                else if new_coeff = 1 then
                  cst
                else
                  assert false in
              Lincons1.set_cst cp cst;
              Lincons1.set_typ cp ty;
              Lincons1.iter (fun coeff var ->
                  let coeff =
                    if new_coeff = -1 then
                      Coeff.neg coeff
                    else if new_coeff = 1 then
                      coeff
                    else
                      assert false in
                  Lincons1.set_coeff cp var coeff) line;
              let a = Lincons1.array_make (Lincons1.get_env cp) 1 in
              Lincons1.array_set a 0 cp;
              let new_c = A.meet_lincons_array man c a in
              p && A.is_leq man new_c b) true opp_typ
        end;
    done;
    !precise


  let join_precise man a b =
    List.fold_left (fun a t ->
        let find_precise_join e =
          let c = A.join man t e in
          if join_is_precise man t e c then
            Some c
          else
            None
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
      ) a b

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
    zip [] c |> join_precise man []


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
    (* FIXME: violent *)
    let c = join_precise man a b in
    (*let c = ref c in
    let d = ref (cleanup_hard man !c) in
    while (List.length !d < List.length !c) do
      let tmp = cleanup_hard man !c in
      c := !d;
      d := tmp;
    done;
    !c*)
    cleanup_hard man c




  let join_list man t =
    match t with
    | [] -> []
    | [t] -> t
    | t::q ->
      List.fold_left (join man) t q
  

  let widening man a b =
    let a = cleanup man a in
    let b = cleanup man b in
    let a =
      join_one man a
    in
    let b =
      join_one man b
    in
    let d = match a, b with
    | None, None -> []
    | None, Some c -> [c]
    | Some c, None -> [c]
    | Some c, Some d ->
        [A.widening man c d]
    in
    d

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

  let push_label man env i t = List.map (A.push_label man env i) t

  let to_lincons_array man t =
    match join_one man t with
    | None -> assert false
    | Some t -> A.to_lincons_array man t

end
