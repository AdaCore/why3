(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

type t = int

let compare x y = compare (x:int) y

type set = int list list

let empty = []

let rec mem (e:int) = function
  | [] -> false
  | h::t -> h = e || mem e t

let get_class t s =
  try
    Some (List.find (mem t) s)
  with
  | Not_found -> None

let change_class t t' s =
  List.rev_map (fun k -> if k == t then t' else k) s

let union a b c =
  let ca = get_class a c in
  let cb = get_class b c in
  match ca, cb with
  | None, Some l ->
      change_class l (a :: l) c
  | Some l, None ->
      change_class l (b :: l) c
  | None, None ->
      if a = b then [a] :: c
      else if a < b then [a; b] :: c
      else [b; a] :: c
  | Some l, Some l' when (l == l') ->
      c
  | Some l, Some l_ ->
      let nl = List.rev_append l l_ |> List.sort_uniq compare in
      List.fold_left (fun acc k ->
          if k == l_ || k == l then acc
          else k :: acc
        ) [nl] c

let sort_uniq l =
  let rec sorted a = function
    | h :: t -> a < h && sorted h t
    | [] -> true in
  match l with
  | [] -> []
  | h :: t ->
      if sorted h t then l
      else List.sort_uniq compare l

let intersect l1 l2 =
  (* intersection of l2 and t'::l1, assuming they are sorted *)
  let rec do_inter (t':int) l1 = function
    | [] -> []
    | t::q ->
        if t = t' then t :: (do_inter t l1 q)
        else if t < t' then do_inter t' l1 q
        else do_inter t q l1 in
  match l1 with
  | t::q -> do_inter t q l2
  | [] -> []

(* join [[1;2;3];[4;5]] [[2];[4;5;6];[7]] = [[2];[4;5];[1];[3];[6];[7]] *)
let join a b =
  let a = List.rev_map sort_uniq a in
  let c =
    List.fold_left (fun l k ->
        let k = sort_uniq k in
        List.fold_left (fun l k' ->
            let i = intersect k k' in
            if i <> [] then i::l else l
          ) l a
      ) [] b in
  let all_elts = List.concat (List.rev_append a b) in
  let known_elts = List.concat c in
  List.fold_left (fun acc t ->
      if mem t known_elts then acc
      else [t] :: acc
    ) c all_elts

let intersect l1 l2 =
  let l1 = sort_uniq l1 in
  let l2 = sort_uniq l2 in
  intersect l1 l2

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
              (List.rev_append ca cb |> List.sort_uniq compare |> List.length) = na
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
      Some t, change_class l nl s


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

let repr a s =
  match get_class a s with
  | None -> a
  | Some s -> List.hd s

let get_class a s =
  match get_class a s with
  | None -> [a]
  | Some s -> s

let fold_class f a s =
  let s = List.rev_map sort_uniq s in
  let fold_single a = function
    | [] -> a
    | t::q ->
      List.fold_left (fun a t' ->
          f a t' t) a q
  in
  List.fold_left fold_single a s

let get_repr s =
  List.map List.hd s
