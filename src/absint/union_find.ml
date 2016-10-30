type t = int

type set = int list list 

let empty = []

let get_class t s =
  try
    Some (List.find (List.mem t) s)
  with
  | Not_found -> None

let union a b c =
  if a = b then 
    c
  else begin
    Format.eprintf "Union of %d and %d.@." a b;
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
      let nl = a::l in
      List.map (fun k ->
          if k == l then
            nl
          else
            k) c
    | None, None ->
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
  end

let join a b =
  List.fold_left (fun a k ->
      match k with
      | [] -> a
      | t::q ->
        List.fold_left (fun a t' ->
            union t t' a) a q
    )  a b

let is_leq a b =
  List.fold_left (fun t cb ->
      t && 
        List.fold_left (fun t ca ->
            t || begin
              let na = List.length ca in
              (ca @ cb |> List.sort_uniq compare |> List.length) = na
            end) false a) true b

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
    | t::q ->
      Some t, List.map (fun k ->
          if k == l then
            nl
          else
            k) s

let print s =
  List.iter (fun k ->
      Format.eprintf "-- [";
      List.iter (fun i ->
          Format.eprintf "%d, " i) k;
      Format.eprintf "]@.";
    ) s;
  Format.eprintf ".@."


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
