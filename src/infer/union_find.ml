type t = int

type set = int list list

let empty = []

let get_class t s =
  try
    Some (List.find (List.mem t) s)
  with
  | Not_found -> None

let union a b c =
  let ca = get_class a c in
  let cb = get_class b c in
  match ca, cb with
  | None, Some l ->
    let nl = a::l in
    List.map (fun k ->
        if k == l then
          nl
        else
          k) c
  | Some l, None ->
    let nl = b::l in
    List.map (fun k ->
        if k == l then
          nl
        else
          k) c
  | None, None ->
    if a = b then
      [a]::c
    else
      [a; b] :: c
  | Some l, Some l' when (l == l') ->
    c
  | Some l, Some l_ ->
    let nl = l @ l_ |> List.sort_uniq compare in
    List.filter (fun k -> not (k == l_)) c
    |> List.map (fun k ->
        if k == l then
          nl
        else
          k)

let intersect l1 l2 =
  let l1 = List.sort_uniq compare l1 in
  let l2 = List.sort_uniq compare l2 in
  (* intersection of l2 and t'::l1 *)
  let rec do_inter t' l1 = function
    | [] -> []
    | t::q -> if t = t' then t::(do_inter t l1 q)
      else if t < t' then
        do_inter t' l1 q
      else
        do_inter t q l1
  in
  match l1 with
  | t::q -> do_inter t q l2
  | [] -> []

let join a b =
  let c = List.fold_left (fun l k ->
      List.fold_left (fun l k' ->
          let i = intersect k k' in
          if i <> [] then
            i::l
          else
            l
        ) l a
    )  [] b
  in
  let all_elts = List.concat (a @ b) in
  let known_elts = List.concat c in
  let all_elts = List.filter (fun t -> not (List.mem t known_elts)) all_elts |> List.map (fun t -> [t]) in
  c @ all_elts

let print s =
  List.iter (fun k ->
      Format.eprintf "-- [";
      List.iter (fun i ->
          Format.eprintf "%d, " i) k;
      Format.eprintf "]@.";
    ) s;
  Format.eprintf ".@."


let is_leq a b =
  let b = List.fold_left (fun t cb ->
      t &&
        List.fold_left (fun t ca ->
            t || begin
              let na = List.length ca in
              (ca @ cb |> List.sort_uniq compare |> List.length) = na
            end) (match cb with [_] -> true | _ -> false) a) true b
  in
  b

let new_class =
  let i = ref 0 in
  fun () ->
    incr i;
    !i

let forget t s =
  let ct = get_class t s in
  match ct with
  | None -> None, s
  | Some l ->
    let nl = List.filter (fun k -> k <> t) l in
    match nl with
    | [] ->
      None, List.filter (fun k -> not (k == l)) s
    | t::_ ->
      Some t, List.map (fun k ->
          if k == l then
            nl
          else
            k) s


let fold_equal f acc (s:set) =
  List.fold_left (fun acc c ->
      let rec browse_list acc = function
        | [] -> acc
        | t::q ->
          let acc = List.fold_left (fun acc e ->
              f acc e t) acc q in
          browse_list acc q
      in
      browse_list acc c
    ) acc s

let flat (s:set) =
  List.concat s

let get_class a s =
  match get_class a s with
  | None -> [a]
  | Some s -> s

let repr a s =
  List.hd (get_class a s)

let fold_class f a s =
  let s = List.map (List.sort_uniq compare) s in
  let fold_single a = function
    | [] -> a
    | t::q ->
      List.fold_left (fun a t' ->
          f a t' t) a q
  in
  List.fold_left fold_single a s

let get_repr s =
  List.map List.hd s
