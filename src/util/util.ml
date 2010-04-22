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

let map_fold_left f acc l =
  let acc, rev =
    List.fold_left
      (fun (acc, rev) e -> let acc, e = f acc e in acc, e :: rev)
      (acc, []) l
  in
  acc, List.rev rev

let list_all2 pr l1 l2 =
  try List.for_all2 pr l1 l2 with Invalid_argument _ -> false

let map_join_left map join = function
  | x :: xl -> List.fold_left (fun acc x -> join acc (map x)) (map x) xl
  | _ -> raise (Failure "map_join_left")

let list_apply f = List.fold_left (fun acc x -> List.rev_append (f x) acc) []

(* boolean fold accumulators *)

exception FoldSkip

let all_fn pr _ t = pr t || raise FoldSkip
let any_fn pr _ t = pr t && raise FoldSkip

(* Set and Map on strings *)

module Sstr = Set.Make(String)
module Mstr = Map.Make(String)

(* Set, Map, Hashtbl on structures with a unique tag and physical equality *)

module type Tagged =
sig
  type t
  val tag : t -> int
end

module OrderedHash (X : Tagged) =
struct
  type t = X.t
  let equal = (==)
  let hash = X.tag
  let compare ts1 ts2 = Pervasives.compare (X.tag ts1) (X.tag ts2)
end

module StructMake (X : Tagged) =
struct
  module T = OrderedHash(X)
  module S = Set.Make(T)
  module M = Map.Make(T)
  module H = Hashtbl.Make(T)
end

