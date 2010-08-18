(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* useful combinators *)

let ($) f x = f x

let const f _ = f

let flip f x y = f y x

(* useful option combinators *)

let of_option = function None -> assert false | Some x -> x

let option_map f = function None -> None | Some x -> Some (f x)

let option_apply d f = function None -> d | Some x -> f x

let option_iter f = function None -> () | Some x -> f x

let option_eq eq a b = match a,b with
  | None, None -> true
  | None, _ | _, None -> false
  | Some x, Some y -> eq x y

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

let list_all2 pr l1 l2 =
  try List.for_all2 pr l1 l2 with Invalid_argument _ -> false

let map_join_left map join = function
  | x :: xl -> List.fold_left (fun acc x -> join acc (map x)) (map x) xl
  | _ -> raise (Failure "map_join_left")

let list_apply f = List.fold_left (fun acc x -> List.rev_append (f x) acc) []

let list_fold_product f acc l1 l2 =
  List.fold_left
    (fun acc e1 ->
       List.fold_left
         (fun acc e2 -> f acc e1 e2)
         acc l2)
    acc l1

let list_fold_product_l f acc ll =
  let ll = List.rev ll in
  let rec aux acc le = function
    | [] -> f acc le
    | l::ll -> List.fold_left (fun acc e -> aux acc (e::le) ll) acc l in
  aux acc [] ll

let list_compare cmp l1 l2 = match l1,l2 with
  | [], [] ->  0
  | [], _  -> -1
  | _,  [] ->  1
  | a1::l1, a2::l2 ->
      let c = cmp a1 a2 in if c = 0 then compare l1 l2 else c

(* boolean fold accumulators *)

exception FoldSkip

let all_fn pr _ t = pr t || raise FoldSkip
let any_fn pr _ t = pr t && raise FoldSkip

(* constant boolean function *)
let ttrue _ = true
let ffalse _ = false

(* Set and Map on ints and strings *)

module Int  = struct type t = int let compare = Pervasives.compare end

module Sint = Set.Make(Int)
module Mint = Map.Make(Int)

module Sstr = Set.Make(String)
module Mstr = Map.Make(String)

(* Set, Map, Hashtbl on structures with a unique tag *)

module type Tagged =
sig
  type t
  val tag : t -> int
end

module type OrderedHash =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module OrderedHash (X : Tagged) =
struct
  type t = X.t
  let hash = X.tag
  let equal ts1 ts2 = X.tag ts1 == X.tag ts2
  let compare ts1 ts2 = Pervasives.compare (X.tag ts1) (X.tag ts2)
end

module OrderedHashList (X : Tagged) =
struct
  type t = X.t list
  let hash = Hashcons.combine_list X.tag 3
  let equ_ts ts1 ts2 = X.tag ts1 == X.tag ts2
  let equal = list_all2 equ_ts
  let cmp_ts ts1 ts2 = Pervasives.compare (X.tag ts1) (X.tag ts2)
  let compare = list_compare cmp_ts
end

module StructMake (X : Tagged) =
struct
  module T = OrderedHash(X)
  module S = Set.Make(T)
  module M = Map.Make(T)
  module H = Hashtbl.Make(T)
end

module MakeTagged (X : Hashweak.Weakey) =
struct
  type t = X.t
  let tag t = Hashweak.tag_hash (X.tag t)
end

module WeakStructMake (X : Hashweak.Weakey) =
struct
  module T = OrderedHash(MakeTagged(X))
  module S = Set.Make(T)
  module M = Map.Make(T)
  module H = Hashtbl.Make(T)
  module W = Hashweak.Make(X)
end

(* memoization *)

let memo_int size f =
  let h = Hashtbl.create size in
  fun x -> try Hashtbl.find h x
  with Not_found -> let y = f x in Hashtbl.add h x y; y

