(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib

(* useful combinators *)

let ($) f x = f x
let (|>) x f = f x

let const f _ = f

let const2 f _ _ = f

let const3 f _ _ _ = f

let flip f x y = f y x

let cons f acc x = (f x)::acc

(* useful iterator on int *)
let rec foldi f acc min max =
  if min > max then acc else foldi f (f acc min) (succ min) max
let mapi f = foldi (fun acc i -> f i::acc) []

(* useful iterator on float *)
let rec iterf f min max step =
  if min > max then () else
    (f min; iterf f (min+.step) max step)

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

let list_apply f l =
  List.rev (List.fold_left (fun acc x -> List.rev_append (f x) acc) [] l)

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
    | l::ll -> List.fold_left (fun acc e -> aux acc (e::le) ll) acc l
  in
  aux acc [] ll

let list_compare cmp l1 l2 = match l1,l2 with
  | [], [] ->  0
  | [], _  -> -1
  | _,  [] ->  1
  | a1::l1, a2::l2 ->
      let c = cmp a1 a2 in if c = 0 then compare l1 l2 else c

let list_flatten_rev fl =
  List.fold_left (fun acc l -> List.rev_append l acc) [] fl

let list_part cmp l =
  let l = List.stable_sort cmp l in
  match l with
    | [] -> []
    | e::l ->
      let rec aux acc curr last = function
        | [] -> ((last::curr)::acc)
        | a::l when cmp last a = 0 -> aux acc (last::curr) a l
        | a::l -> aux ((last::curr)::acc) [] a l in
      aux [] [] e l

let rec list_first f = function
  | [] -> raise Not_found
  | a::l -> match f a with
      | None -> list_first f l
      | Some r -> r

let list_find_nth p l =
  let rec aux p n = function
    | [] -> raise Not_found
    | a::l -> if p a then n else aux p (n+1) l in
  aux p 0 l


let list_first_nth f l =
  let rec aux f n = function
    | [] -> raise Not_found
    | a::l -> match f a with
      | None -> aux f (n+1) l
      | Some r -> n,r in
  aux f 0 l

let list_iteri f l =
  let rec iter i = function
    | [] -> ()
    | x :: l -> f i x; iter (i + 1) l
  in
  iter 0 l

let list_mapi f l =
  let rec map i = function
    | [] -> []
    | x :: l -> let v = f i x in v :: map (i + 1) l
  in
  map 0 l

let list_fold_lefti f acc l =
  let rec fold_left acc i = function
    | [] -> acc
    | a :: l -> fold_left (f acc i a) (i + 1) l
  in
  fold_left acc 0 l

let list_or f l =
  List.fold_left (fun acc e -> f e || acc) false l

let list_and f l =
  List.fold_left (fun acc e -> f e && acc) true l

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

(* boolean fold accumulators *)

exception FoldSkip

let all_fn pr _ t = pr t || raise FoldSkip
let any_fn pr _ t = pr t && raise FoldSkip

(* constant boolean function *)
let ttrue _ = true
let ffalse _ = false

(* useful function on string *)
let split_string_rev s c =
  let rec aux acc i =
    try
      let j = String.index_from s i c in
      aux ((String.sub s i (j-i))::acc) (j + 1)
    with Not_found -> (String.sub s i (String.length s - i))::acc
      | Invalid_argument _ -> ""::acc in
  aux [] 0

let ends_with s suf =
  let rec aux s suf suflen offset i =
    i >= suflen || (s.[i + offset] = suf.[i]
                   && aux s suf suflen offset (i+1)) in
  let slen = String.length s in
  let suflen = String.length suf in
  slen >= suflen && aux s suf suflen (slen - suflen) 0

let padd_string c s i =
  let sl = String.length s in
  if sl < i then
    let p = String.create i in
    String.blit s 0 p 0 sl;
    String.fill p sl (i-sl) c;
    p
  else if sl > i
  then String.sub s 0 i
  else s

(** useful function on char *)
let is_uppercase c = 'A' <= c && c <= 'Z'

let concat_non_empty sep l =
  String.concat sep (List.filter (fun s -> s <> "") l)

(** useful function on char *)
let count n =
  let r = ref (n-1) in
  fun _ -> incr r; !r

(* Set and Map on ints and strings *)

module Int  = struct
  type t = int
  let compare = Pervasives.compare
  let equal x y = x = y
  let hash x = x
 end

module Mint = Map.Make(Int)
module Sint = Mint.Set
module Hint = Hashtbl.Make(Int)

module Mstr = Map.Make(String)
module Sstr = Mstr.Set
module Hstr = Hashtbl.Make
  (struct
    type t = String.t
    let hash    = (Hashtbl.hash : string -> int)
    let equal   = ((=) : string -> string -> bool)
  end)

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
  module M = Map.Make(T)
  module S = M.Set
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
  module M = Map.Make(T)
  module S = M.Set
  module H = Hashtbl.Make(T)
  module W = Hashweak.Make(X)
end

module type PrivateHashtbl = sig
  (** Private Hashtbl *)
  type 'a t
  type key

  val find : 'a t -> key -> 'a
    (** Same as {Hashtbl.find} *)
  val iter : (key -> 'a -> unit) -> 'a t -> unit
    (** Same as {Hashtbl.iter} *)
  val fold : (key -> 'a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc
    (** Same as {Hashtbl.fold} *)
  val mem : 'a t -> key -> bool
    (** Same as {Hashtbl.mem} *)
  val length : 'a t -> int
    (** Same as {Hashtbl.length} *)

end

module type PrivateArray = sig
  (** Private Array *)
  type 'a t

  val get : 'a t -> int -> 'a
  val iter : ('a -> unit) -> 'a t -> unit
    (** Same as {!Array.iter} *)
  val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
    (** Same as {!Array.fold} *)

end
