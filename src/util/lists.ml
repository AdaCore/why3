(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* useful list combinators *)

let rev_map_fold_left f acc l =
  let acc, rev =
    List.fold_left
      (fun (acc, rev) e -> let acc, e = f acc e in acc, e :: rev)
      (acc, []) l
  in
  acc, rev

let map_fold_left f acc l =
  let acc, rev = rev_map_fold_left f acc l in
  acc, List.rev rev

let map_fold_right f l acc =
  List.fold_right
    (fun e (l, acc) -> let e, acc = f e acc in e :: l, acc)
    l ([], acc)

let map_filter f l =
  List.fold_right
    (fun e l -> match f e with Some e -> e :: l | None -> l)
    l []

let equal pr l1 l2 =
  try List.for_all2 pr l1 l2 with Invalid_argument _ -> false

let rec compare cmp l1 l2 = match l1,l2 with
  | [], [] ->  0
  | [], _  -> -1
  | _,  [] ->  1
  | a1::l1, a2::l2 ->
      let c = cmp a1 a2 in if c = 0 then compare cmp l1 l2 else c

let map_join_left map join = function
  | x :: xl -> List.fold_left (fun acc x -> join acc (map x)) (map x) xl
  | _ -> invalid_arg "List.Lists.map_join_left"

let apply f l =
  List.rev (List.fold_left (fun acc x -> List.rev_append (f x) acc) [] l)

let cons f acc x = (f x)::acc

let fold_product f acc l1 l2 =
  List.fold_left
    (fun acc e1 ->
       List.fold_left
         (fun acc e2 -> f acc e1 e2)
         acc l2)
    acc l1

let fold_product_l f acc ll =
  let ll = List.rev ll in
  let rec aux acc le = function
    | [] -> f acc le
    | l::ll -> List.fold_left (fun acc e -> aux acc (e::le) ll) acc l
  in
  aux acc [] ll

let flatten_rev fl =
  List.fold_left (fun acc l -> List.rev_append l acc) [] fl

let part cmp l =
  let l = List.stable_sort cmp l in
  match l with
    | [] -> []
    | e::l ->
      let rec aux acc curr last = function
        | [] -> ((last::curr)::acc)
        | a::l when cmp last a = 0 -> aux acc (last::curr) a l
        | a::l -> aux ((last::curr)::acc) [] a l in
      aux [] [] e l

let rec first f = function
  | [] -> raise Not_found
  | a::l -> match f a with
      | None -> first f l
      | Some r -> r

let find_nth p l =
  let rec aux p n = function
    | [] -> raise Not_found
    | a::l -> if p a then n else aux p (n+1) l in
  aux p 0 l


let first_nth f l =
  let rec aux f n = function
    | [] -> raise Not_found
    | a::l -> match f a with
      | None -> aux f (n+1) l
      | Some r -> n,r in
  aux f 0 l

let iteri f l =
  let rec iter i = function
    | [] -> ()
    | x :: l -> f i x; iter (i + 1) l
  in
  iter 0 l

let mapi f l =
  let rec map i = function
    | [] -> []
    | x :: l -> let v = f i x in v :: map (i + 1) l
  in
  map 0 l

let fold_lefti f acc l =
  let rec fold_left acc i = function
    | [] -> acc
    | a :: l -> fold_left (f acc i a) (i + 1) l
  in
  fold_left acc 0 l

let rec prefix n l =
  if n = 0 then []
  else if n < 0 || l = [] then invalid_arg "Util.chop"
  else List.hd l :: prefix (n - 1) (List.tl l)

let rec chop n l =
  if n = 0 then l
  else if n < 0 || l = [] then invalid_arg "Util.chop"
  else chop (n - 1) (List.tl l)

let rec chop_last = function
  | [] -> invalid_arg "Util.chop_last"
  | [r] -> [], r
  | x :: s -> let s, r = chop_last s in x :: s, r
