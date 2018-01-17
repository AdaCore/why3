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

module type S = sig
  module M : Extmap.S
  type elt = M.key
  type t = unit M.t
  val empty: t
  val is_empty: t -> bool
  val mem: elt -> t -> bool
  val add: elt -> t -> t
  val singleton: elt -> t
  val remove: elt -> t -> t
  val merge: (elt -> bool -> bool -> bool) -> t -> t -> t
  val compare: t -> t -> int
  val equal: t -> t -> bool
  val subset: t -> t -> bool
  val disjoint: t -> t -> bool
  val iter: (elt -> unit) -> t -> unit
  val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all: (elt -> bool) -> t -> bool
  val exists: (elt -> bool) -> t -> bool
  val filter: (elt -> bool) -> t -> t
  val partition: (elt -> bool) -> t -> t * t
  val cardinal: t -> int
  val elements: t -> elt list
  val min_elt: t -> elt
  val max_elt: t -> elt
  val choose: t -> elt
  val split: elt -> t -> t * bool * t
  val change : (bool -> bool) -> elt -> t -> t
  val union : t -> t -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val fold_left : ('b -> elt -> 'b) -> 'b -> t -> 'b
  val fold2_inter : (elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
  val fold2_union : (elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
  val translate : (elt -> elt) -> t -> t
  val add_new : exn -> elt -> t -> t
  val is_num_elt : int -> t -> bool
  val of_list : elt list -> t
  val contains: t -> elt -> bool
  val add_left: t -> elt -> t
  val remove_left: t -> elt -> t
  val print: (Format.formatter -> elt -> unit) -> Format.formatter -> t -> unit
end

module MakeOfMap (M: Extmap.S) = struct
  module M = M
  type elt = M.key
  type t = unit M.t

  let is_true b = if b then Some () else None

  let empty = M.empty
  let is_empty = M.is_empty
  let mem = M.mem
  let add e s = M.add e () s
  let singleton e = M.singleton e ()
  let remove = M.remove
  let merge f s t =
    M.merge (fun e a b -> is_true (f e (a <> None) (b <> None))) s t
  let compare = M.set_compare
  let equal = M.set_equal
  let subset = M.set_submap
  let disjoint = M.set_disjoint
  let iter f s = M.iter (fun e _ -> f e) s
  let fold f s acc = M.fold (fun e _ -> f e) s acc
  let for_all f s = M.for_all (fun e _ -> f e) s
  let exists f s = M.exists (fun e _ -> f e) s
  let filter f s = M.filter (fun e _ -> f e) s
  let partition f s = M.partition (fun e _ -> f e) s
  let cardinal = M.cardinal
  let elements = M.keys
  let min_elt t = fst (M.min_binding t)
  let max_elt t = fst (M.max_binding t)
  let choose t = fst (M.choose t)
  let split e t = let l,m,r = M.split e t in l,(m <> None),r
  let change f x s = M.change (fun a -> is_true (f (a <> None))) x s
  let union = M.set_union
  let inter = M.set_inter
  let diff = M.set_diff
  let fold_left f acc s = M.fold_left (fun acc k () -> f acc k) acc s
  let fold2_inter f s t acc = M.fold2_inter (fun k _ _ acc -> f k acc) s t acc
  let fold2_union f s t acc = M.fold2_union (fun k _ _ acc -> f k acc) s t acc
  let translate = M.translate
  let add_new e x s = M.add_new e x () s
  let is_num_elt n m = M.is_num_elt n m
  let of_list l = List.fold_left (fun acc a -> add a acc) empty l
  let contains = M.contains
  let add_left s e = M.add e () s
  let remove_left s e = M.remove e s
  let print print_elt fmt s =
    if is_empty s then Format.fprintf fmt "{}" else begin
      Format.fprintf fmt "@[<hov 2>{ ";
      Pp.print_iter1 iter Pp.comma print_elt fmt s;
      Format.fprintf fmt "}@]"
    end
end

module type OrderedType = Set.OrderedType

module Make(Ord: OrderedType) = MakeOfMap(Extmap.Make(Ord))
