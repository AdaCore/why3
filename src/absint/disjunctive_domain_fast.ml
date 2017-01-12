open Domain

type 'a a = { t: 'a list; c: bool; i: int; }

module type D = sig
  include DOMAIN
  val round_integers: man -> env -> t -> t
end

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
    try
      Hashdoml.find (snd man).meet_lincons (a, l, fst man)
    with
    | Not_found ->
      let c = A.meet_lincons_array (fst man) a l in
      (* Hashdoml.add (snd man).meet_lincons (a, l, fst man) c; *)
      c

  let a_is_leq man a b =
    A.is_leq (fst man) a b
  
  let a_join man a b =
    try
      Hashdom.find (snd man).real_join_tbl (a, b, fst man)
    with
    | Not_found ->
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
    
  let rec int_of_s s =
      let open Apron.Scalar in
      match s with
      | Float f -> 
        let i = int_of_float f in
        assert (float_of_int i = f);
        i
      | Mpqf t ->
        int_of_s (Float (Mpqf.to_float t))
      | Mpfrf t ->
        int_of_s (Float (Mpfr.to_float t))

  let round_integers_a (man, _) env a =
    let open Apron in
    let l = A.to_lincons_array man a in
    let n = Apron.Lincons1.array_length l in
    let a = ref a in
    for i = 0 to n -1 do
      let l = Lincons1.array_get l i in
      let n = ref 0 in
      if not (Coeff.equal_int (Lincons1.get_cst l) 0) then
        begin
          let i = Lincons1.get_cst l |> function
            | Coeff.Scalar(s) ->
              int_of_s s
            | _ -> assert false
          in
          let l' = Lincons1.copy l in
          Lincons1.iter (fun c v ->
              if not (Coeff.equal_int c 0) then
                begin

                  let myi = match c with
                    | Coeff.Scalar(s) ->
                      let s = Scalar.to_string s in
                      int_of_string s
                    | _ -> assert false
                  in
                  Lincons1.set_coeff l' v (Coeff.s_of_int (if myi < 0 then -1 else 1));
                  let c = 
                    if i mod myi = 0 then
                      i/(abs myi)
                    else if i > 0 then i/(abs myi)
                    else i/(abs myi) - 1
                  in

                  Lincons1.set_cst l' (Coeff.s_of_int c);
                  incr n;
                end
            ) l;
          if !n = 1 then
            begin
              let ar = Lincons1.array_make env 1 in
              Lincons1.array_set ar 0 l';
              a := A.meet_lincons_array man !a ar
            end
        end
    done;
    !a

  let round_integers m e a = { a with t = List.map (round_integers_a m e) a.t }


  let join_one man { t; i; _ } =
    match t with
    | [] -> bottom () ()
    | t::q -> { t = [List.fold_left (a_join man) t q]; c = true; i; }

  let join_is_precise man a b c =
    try
      Hashdom.find (snd man).join_tbl (a, b, (fst man))
    with
    | Not_found ->
      let man' = man in
    let man = fst man in
    let open Apron in
    let linexpr_a = A.to_lincons_array man a in
    let linexpr_b = A.to_lincons_array man b in
    let a, b, linexpr_a, linexpr_b =
      if Lincons1.array_length linexpr_a > Lincons1.array_length linexpr_b then
        b, a, linexpr_b, linexpr_a
      else
        a, b, linexpr_a, linexpr_b
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
              p &&
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
              let new_c = a_meet_lincons_array man' c a in
              let new_c = round_integers_a (man, man') (Lincons1.get_env cp) new_c in
              a_is_leq man' new_c b) true opp_typ
        end;
    done;
      (*Hashdom.add (snd man').join_tbl (a, b, man) !precise; *)
    !precise


  let join_precise man a b =
    { t = List.fold_left (fun a t ->
        let find_precise_join e =
          let c = a_join man t e in
          if join_is_precise man t e c then
            begin
            Some c
            end
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
    let t = cleanup_hard man t in
    let f = A.to_term env pmod in
    let t = List.map (fun t -> f (fst man) t var_mapping) t.t
    |> Term.t_or_simp_l in
    t

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
