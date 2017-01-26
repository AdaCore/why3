open Domain

module Make(S:sig
    module A:TERM_DOMAIN
    val env: Env.env
    val pmod: Pmodule.pmodule
  end) = struct
  module A = S.A
  module D = A
  
  open Ai_logic
  module Ai_logic = Ai_logic.Make(struct
      let env = S.env
      let pmod = S.pmod
    end)
  open Ai_logic
  
  type man = A.man
  type env = A.env

  let create_manager = A.create_manager

  let hash _ _ = assert false
  let is_eq _ _ _ = assert false
  
  let bottom m e = []

  let top m e = [A.top m e]

  let canonicalize m _ = () (*List.iter (A.canonicalize m)*)
  
  let print fmt = List.iter (fun b ->
      A.print fmt b;
      Format.fprintf fmt "@.";)

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

  let threshold = 10


  let join_one man = function
    | [] -> None
    | t::q -> Some (List.fold_left (A.join man) t q)

  let unwrap_domain = function
    | None -> []
    | Some t -> [t]

  let join_precise man a b =
    List.fold_left (fun a t ->
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
  

  (* used once by loop, so it can be costly *)
  let widening man a b =
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
    let b_leq = List.map (fun b ->
        b, try
          List.find (fun a ->
              A.is_leq man a b) a
        with
        | Not_found -> b
      ) b
    in
    List.map (fun (k, v) ->
        A.widening man v k) b_leq |> cleanup man

  let to_term man t =
    let t = List.map (fun t -> A.to_term man t) t
    |> Term.t_or_simp_l in
    t

  let push_label man env i t = List.map (A.push_label man env i) t
  
  let rec meet_term man term elt =
    let open Term in
    match term.t_node with
    | Tbinop(Tor, a, b) ->
      join man (meet_term man a elt) (meet_term man b elt)
    | Tbinop(Tand, a, b) ->
      meet_term man a elt |> meet_term man b
    | Tbinop(_) -> assert false
    | _ -> List.map (A.meet_term man term) elt

  let forget_var man vs t =
    List.map (A.forget_var man vs) t
  
  let forget_term man vs t =
    List.map (A.forget_term man vs) t
  
  let forget_region man reg m t =
    List.map (A.forget_region man reg m) t

  let add_variable_to_env = A.add_variable_to_env
  let add_lvariable_to_env = A.add_lvariable_to_env
  let is_join_precise man a b =
    Some (join man a b)
  let make_consistent man a b = failwith "not implemented"
end
