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

(** Hash-consed Patricia Trees *)

module type M = sig
  type key
  type value

  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val id : t -> int

  val empty : t
  val is_empty : t -> bool
  val mem : key -> t -> bool
  val find : key -> t -> value
  val find_opt : key -> t -> value option
  val add : key -> value -> t -> t
  val singleton : key -> value -> t
  val remove : key -> t -> t
  val cardinal : t -> int
  val iter : (key -> value -> unit) -> t -> unit
  val fold : (key -> value -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_left : ('a -> key -> value -> 'a) -> 'a -> t -> 'a
  val fold_right : (key -> value -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all : (key -> value -> bool) -> t -> bool
  val exists : (key -> value -> bool) -> t -> bool
  val filter : (key -> value -> bool) -> t -> t
  val filter_map : (key -> value -> value option) -> t -> t
  val partition : (key -> value -> bool) -> t -> t * t
  val min_binding : t -> key * value
  val min_binding_opt : t -> (key * value) option
  val max_binding : t -> key * value
  val max_binding_opt : t -> (key * value) option
  val choose : t -> key * value
  val choose_opt : t -> (key * value) option
  val split : key -> t -> t * value option * t
  val keys : t -> key list
  val bindings : t -> (key * value) list
  val compare : (value -> value -> int) -> t -> t -> int
(*
  val merge :
    (key -> value option -> value option -> value option) ->
    t -> t -> t
  val update : key -> (value option -> value option) -> t -> t
  val union :
    (key -> value -> value -> value option) -> t -> t -> t
  val inter :
    (key -> value -> value -> value option) -> t -> t -> t
  val diff :
    (key -> value -> value -> value option) -> t -> t -> t
*)
  val to_seq : t -> (key * value) Seq.t
  val to_seq_from : key -> t -> (key * value) Seq.t
  val add_seq : (key * value) Seq.t -> t -> t
  val of_seq : (key * value) Seq.t -> t
end

module type S = sig
  type elt

  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val id : t -> int

  val empty : t
  val is_empty : t -> bool
  val mem : elt -> t -> bool
  val add : elt -> t -> t
  val singleton : elt -> t
  val remove : elt -> t -> t
  val cardinal : t -> int
  val iter : (elt -> unit) -> t -> unit
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_left : ('a -> elt -> 'a) -> 'a -> t -> 'a
  val fold_right : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all : (elt -> bool) -> t -> bool
  val exists : (elt -> bool) -> t -> bool
  val filter : (elt -> bool) -> t -> t
  val partition : (elt -> bool) -> t -> t * t
  val min_elt : t -> elt
  val min_elt_opt : t -> elt option
  val max_elt : t -> elt
  val max_elt_opt : t -> elt option
  val choose : t -> elt
  val choose_opt : t -> elt option
  val split : elt -> t -> t * bool * t
  val elements : t -> elt list
  val compare : t -> t -> int
(*
  val merge : (elt -> bool -> bool -> bool) -> t -> t -> t
  val union : t -> t -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val disjoint : t -> t -> bool
*)
  val to_seq : t -> elt Seq.t
  val to_seq_from : elt -> t -> elt Seq.t
  val add_seq : elt Seq.t -> t -> t
  val of_seq : elt Seq.t -> t
end

module MakeMap(X: sig
  type t
  val id: t -> int
  type value
  val hash: value -> int
  val equal: value -> value -> bool
end) = struct

  type key = X.t
  type value = X.value
  type uid = int

  type t =
    | Empty
    | Leaf of uid * key * value
    | Branch of uid * int * int * t * t

  (**** hash-consing machinery starts here... ********************************)
  let hash = function
    | Empty -> 0
    | Leaf (id, _, _) | Branch (id, _, _, _, _) -> id

  let equal: t -> t -> bool =
    (==)

  module H = Ephemeron.K1.Make(struct
    type nonrec t = t
    let hash = function
      | Empty -> 0
      | Leaf (_, k, v) -> 31 * X.id k + X.hash v
      | Branch (_, p, _, t0, t1) -> 19 * (19 * p + hash t0) + hash t1
    let equal t0 t1 = match t0, t1 with
      | Empty, Empty -> true
      | Leaf (_, k0, v0), Leaf (_, k1, v1) ->
          X.id k0 = X.id k1 && X.equal v0 v1
      | Branch (_, p0, m0, t00, t01), Branch (_, p1, m1, t10, t11) ->
          p0 == p1 && m0 == m1 && t00 == t10 && t01 == t11
      | _ -> false
  end)
  let table = H.create 8192
  let nextid = ref 1
  let hashcons n =
    try H.find table n
    with Not_found -> incr nextid; H.add table n n; n
  let leaf (k, v) = hashcons (Leaf (!nextid, k, v))
  let branch (p, m, t0, t1) = hashcons (Branch (!nextid, p, m, t0, t1))
  (**** ... and stops here ***************************************************)

  (* Hacker's Delight 7.1 *)
  let bit_reversal16 x =
    let x = ((x land 0x5555) lsl 1) lor ((x lsr 1) land 0x5555) in
    let x = ((x land 0x3333) lsl 2) lor ((x lsr 2) land 0x3333) in
    let x = ((x land 0x0F0F) lsl 4) lor ((x lsr 4) land 0x0F0F) in
    ((x land 0xFF) lsl 8) lor (x lsr 8)

  let bit_reversal31 x =
    ((bit_reversal16 (x land 0xFFFF)) lsl 15) lor
    ((bit_reversal16 (x lsr 16)) lsr 1)

  let bit_reversal32 x =
    let ox55555555 = (0x5555 lsl 16) lor 0x5555 in
    let x = ((x land ox55555555) lsl 1) lor ((x lsr 1) land ox55555555) in
    let x = ((x land 0x33333333) lsl 2) lor ((x lsr 2) land 0x33333333) in
    let x = ((x land 0x0F0F0F0F) lsl 4) lor ((x lsr 4) land 0x0F0F0F0F) in
    ((x land 0xFF) lsl 24) lor ((x land 0xFF00) lsl 8) lor
    ((x lsr 8) land 0xFF00) lor (x lsr 24)

  let bit_reversal63 x =
    let oxFFFFFFFF = (0xFFFF lsl 16) lor 0xFFFF in
    ((bit_reversal32 (x land oxFFFFFFFF)) lsl 31) lor
    ((bit_reversal32 (x lsr 32)) lsr 1)

  let bit_reversal = match Sys.word_size with
    | 32 -> bit_reversal31
    | 64 -> bit_reversal63
    | _ -> assert false

  let bits k =
    bit_reversal ((X.id k) lxor min_int)

  let empty =
    Empty

  let is_empty t =
    t = Empty

  let zero_bit k m =
    (k land m) == 0

  let lowest_bit x =
    x land (-x)

  let branching_bit p0 p1 =
    lowest_bit (p0 lxor p1)

  let mask p m =
    p land (m-1)

  let match_prefix bk p m =
    (mask bk m) == p

  let rec mem bk = function
    | Empty -> false
    | Leaf (_, j,_) -> bk == bits j
    | Branch (_, p, m, l, r) ->
        match_prefix bk p m &&
        mem bk (if zero_bit bk m then l else r)

  let mem k t =
    mem (bits k) t

  let rec find bk = function
    | Empty -> raise Not_found
    | Leaf (_, j,x) -> if bk == bits j then x else raise Not_found
    | Branch (_, p, m, l, r) ->
        if not (match_prefix bk p m) then raise Not_found;
        find bk (if zero_bit bk m then l else r)

  let find k t =
    find (bits k) t

  let find_opt k m = try Some (find k m) with Not_found -> None

  let join (p0,t0,p1,t1) =
    let m = branching_bit p0 p1 in
    if zero_bit p0 m then
      branch (mask p0 m, m, t0, t1)
    else
      branch (mask p0 m, m, t1, t0)

  let add k x t =
    let bk = bits k in
    let rec ins = function
      | Empty -> leaf (k,x)
      | Leaf (_,j,_) as t ->
          let bj = bits j in
          if bj == bk then leaf (k,x)
          else join (bk, leaf (k,x), bj, t)
      | Branch (_,p,m,t0,t1) as t ->
          if match_prefix bk p m then
            if zero_bit bk m then
              branch (p, m, ins t0, t1)
            else
              branch (p, m, t0, ins t1)
          else
            join (bk, leaf (k,x), p, t)
    in
    ins t

  let singleton k v =
    add k v empty

  let branch = function
    | (_,_,Empty,t) -> t
    | (_,_,t,Empty) -> t
    | (p,m,t0,t1)   -> branch (p,m,t0,t1)

  let remove k t =
    let bk = bits k in
    let rec rmv = function
      | Empty -> Empty
      | Leaf (_,j,_) as t -> if bk == bits j then Empty else t
      | Branch (_,p,m,t0,t1) as t ->
          if match_prefix bk p m then
            if zero_bit bk m then
              branch (p, m, rmv t0, t1)
            else
              branch (p, m, t0, rmv t1)
          else
            t
    in
    rmv t

  let rec cardinal = function
    | Empty -> 0
    | Leaf _ -> 1
    | Branch (_, _,_,t0,t1) -> cardinal t0 + cardinal t1

  let rec iter f = function
    | Empty -> ()
    | Leaf (_, k,x) -> f k x
    | Branch (_, _,_,t0,t1) -> iter f t0; iter f t1

  let rec fold f s accu = match s with
    | Empty -> accu
    | Leaf (_, k,x) -> f k x accu
    | Branch (_, _,_,t0,t1) -> fold f t1 (fold f t0 accu)

  let rec fold_left f accu s = match s with
    | Empty -> accu
    | Leaf (_, k,x) -> f accu k x
    | Branch (_, _,_,t0,t1) -> fold_left f (fold_left f accu t0) t1

  let rec fold_right f s accu = match s with
    | Empty -> accu
    | Leaf (_, k,x) -> f k x accu
    | Branch (_, _,_,t0,t1) -> fold_right f t0 (fold_right f t1 accu)

  let rec for_all p = function
    | Empty -> true
    | Leaf (_, k, v)  -> p k v
    | Branch (_, _,_,t0,t1) -> for_all p t0 && for_all p t1

  let rec exists p = function
    | Empty -> false
    | Leaf (_, k, v) -> p k v
    | Branch (_, _,_,t0,t1) -> exists p t0 || exists p t1

  let rec filter pr = function
    | Empty -> Empty
    | Leaf (_, k, v) as t -> if pr k v then t else Empty
    | Branch (_, p,m,t0,t1) -> branch (p, m, filter pr t0, filter pr t1)

  let rec filter_map pr = function
    | Empty -> Empty
    | Leaf (_, k, v) -> (match pr k v with Some v' -> leaf (k, v') | None -> Empty)
    | Branch (_, p,m,t0,t1) -> branch (p, m, filter_map pr t0, filter_map pr t1)

  (* FIXME? *)
  let partition p s =
    let rec part (t,f as acc) = function
      | Empty -> acc
      | Leaf (_,k,v) -> if p k v then (add k v t, f) else (t, add k v f)
      | Branch (_, _,_,t0,t1) -> part (part acc t0) t1
    in
    part (Empty, Empty) s

  let rec min_binding = function
    | Empty -> raise Not_found
    | Leaf (_, k, v) -> (k, v)
    | Branch (_, _, _, t0, _) -> min_binding t0

  let rec min_binding_opt = function
    | Empty -> None
    | Leaf (_, k, v) -> Some (k, v)
    | Branch (_, _, _, t0, _) -> min_binding_opt t0

  let rec max_binding = function
    | Empty -> raise Not_found
    | Leaf (_, k, v) -> (k, v)
    | Branch (_, _, _, _, t1) -> max_binding t1

  let rec max_binding_opt = function
    | Empty -> None
    | Leaf (_, k, v) -> Some (k, v)
    | Branch (_, _, _, _, t1) -> max_binding_opt t1

  let choose = min_binding

  let choose_opt = min_binding_opt

  let prefix = function
    | Empty -> assert false
    | Leaf (_, k, _) -> bits k
    | Branch (_, p, _, _, _) -> p

  (* concat (t0, t1) under the assumption t0 < t1 *)
  let concat = function
    | Empty, t | t, Empty -> t
    | t0, t1 ->
        let p0 = prefix t0 in
        let p1 = prefix t1 in
        assert (p0 != p1);
        let m = branching_bit p0 p1 in
        branch (mask p0 m, m, t0, t1)

  let split x t =
    let bx = bits x in
    let rec split = function
      | Empty -> Empty, None, Empty
      | Leaf (_, k, v) as t ->
          let c = Stdlib.compare (X.id x) (X.id k) in
          if c < 0 then Empty, None, t
          else if c = 0 then Empty, Some v, Empty
          else t, None, Empty
      | Branch (_, p, m, t0, t1) as t ->
          if match_prefix bx p m then
            if zero_bit bx m then
              let t00, o, t01 = split t0 in
              t00, o, concat (t01, t1)
            else
              let t10, o, t11 = split t1 in
              concat (t0, t10), o, t11
          else
            let m = branching_bit bx p in
            if zero_bit bx m then Empty, None, t else t, None, Empty
    in
    split t

  let keys m =
    fold_right (fun k _ acc -> k :: acc) m []

  let bindings m =
    fold_right (fun k v acc -> (k, v) :: acc) m []

  (* ~ unsigned_compare (rev b1) (rev b2) *)
  let compare_bits b1 b2 =
    if b1 = b2 then 0 else
    let m = branching_bit b1 b2 in
    if zero_bit b1 m then -1 else 1

  (* we order constructors as Empty < Leaf < Branch *)
  let compare cmp t1 t2 =
    let rec compare_aux t1 t2 = match t1,t2 with
      | Empty, Empty -> 0
      | Empty, _ -> -1
      | _, Empty -> 1
      | Leaf (_, k1,x1), Leaf (_, k2,x2) ->
          let c = Stdlib.compare (X.id k1) (X.id k2) in
          if c <> 0 then c else cmp x1 x2
      | Leaf _, Branch _ -> -1
      | Branch _, Leaf _ -> 1
      | Branch (_, p1,m1,l1,r1), Branch (_, p2,m2,l2,r2) ->
          let c = compare_bits p1 p2 in
          if c <> 0 then c else
          let c = compare_bits m1 m2 in
          if c <> 0 then c else
          let c = compare_aux l1 l2 in
          if c <> 0 then c else
          compare_aux r1 r2
    in
    compare_aux t1 t2

(*
  let merge f m1 m2 =
    let add m k = function None -> m | Some v -> add k v m in
    (* first consider all bindings in m1 *)
    let m = fold
        (fun k1 v1 m -> add m k1 (f k1 (Some v1) (find_opt k1 m2))) m1 empty in
    (* then bindings in m2 that are not in m1 *)
    fold (fun k2 v2 m -> if mem k2 m1 then m else add m k2 (f k2 None (Some v2)))
      m2 m

  let update x f m =
    match f (find_opt x m) with
    | None -> remove x m
    | Some z -> add x z m

  let unsigned_lt n m = n >= 0 && (m < 0 || n < m)

  let rec union f = function
    | Empty, t  -> t
    | t, Empty  -> t
    | Leaf (_, k,v1), t ->
        update k (function None -> Some v1 | Some v2 -> f k v1 v2) t
    | t, Leaf (_, k,v2) ->
        update k (function None -> Some v2 | Some v1 -> f k v1 v2) t
    | (Branch (_, p,m,s0,s1) as s), (Branch (_, q,n,t0,t1) as t) ->
        if m == n && match_prefix q p m then
          (* The trees have the same prefix. Merge the subtrees. *)
          branch (p, m, union f (s0,t0), union f (s1,t1))
        else if unsigned_lt m n && match_prefix q p m then
          (* [q] contains [p]. Merge [t] with a subtree of [s]. *)
          if zero_bit q m then
            branch (p, m, union f (s0,t), s1)
          else
            branch (p, m, s0, union f (s1,t))
        else if unsigned_lt n m && match_prefix p q n then
          (* [p] contains [q]. Merge [s] with a subtree of [t]. *)
          if zero_bit p n then
            branch (q, n, union f (s,t0), t1)
          else
            branch (q, n, t0, union f (s,t1))
        else
          (* The prefixes disagree. *)
          join (p, s, q, t)

  let union f s t = union f (s,t)
*)

  let to_seq m =
    let rec prepend_seq m s = match m with
      | Empty -> s
      | Leaf (_, k, v) -> fun () -> Seq.Cons((k,v), s)
      | Branch (_, _, _, l, r) -> prepend_seq l (prepend_seq r s)
    in
    prepend_seq m Seq.empty

  let to_seq_from k m =
    let rec prepend_seq m s = match m with
      | Empty -> s
      | Leaf (_, key, v) -> if key >= k then fun () -> Seq.Cons((key,v), s) else s
      | Branch (_, _, _, l, r) -> prepend_seq l (prepend_seq r s)
    in
    prepend_seq m Seq.empty

  let add_seq s m =
    Seq.fold_left (fun m (k, v) -> add k v m) m s

  let of_seq s =
    Seq.fold_left (fun m (k, v) -> add k v m) empty s

  let id = hash

end

module MakeSet(X : sig
  type t
  val id : t -> int
end) = struct
  module M = MakeMap(struct
    include X
    type value = unit
    let hash _ = 42
    let equal _ _ = true
  end)

  type elt = X.t
  type t = M.t

  let hash = M.hash
  let equal = M.equal
  let id = M.id

  let empty = M.empty
  let is_empty = M.is_empty
  let mem = M.mem
  let add x t = M.add x () t
  let singleton x = M.singleton x ()
  let remove = M.remove
  let cardinal = M.cardinal
  let iter f t = M.iter (fun x _ -> f x) t
  let fold f t acc = M.fold (fun x _ acc -> f x acc) t acc
  let fold_left f acc t = M.fold_left (fun acc x _ -> f acc x) acc t
  let fold_right f t acc = M.fold_right (fun x _ acc -> f x acc) t acc
  let for_all p t = M.for_all (fun x _ -> p x) t
  let exists p t = M.exists (fun x _ -> p x) t
  let filter p t = M.filter (fun x _ -> p x) t
  let partition p t = M.partition (fun x _ -> p x) t
  let min_elt t = fst (M.min_binding t)
  let min_elt_opt t = Option.map fst (M.min_binding_opt t)
  let max_elt t = fst (M.max_binding t)
  let max_elt_opt t = Option.map fst (M.max_binding_opt t)
  let choose t = fst (M.choose t)
  let choose_opt t = Option.map fst (M.choose_opt t)
  let split x t = let l, o, r = M.split x t in l, o<>None, r
  let elements = M.keys
  let compare t1 t2 = M.compare (fun _ _ -> 0) t1 t2
(*
  let merge f t1 t2 =
    M.merge (fun x o1 o2 ->
        if f x (o1<>None) (o2<>None) then Some () else None)
      t1 t2
  let union = M.union (fun _ _ _ -> Some ())
  let inter = merge (fun _ b1 b2 -> b1 && b2)
  let diff = merge (fun _ b1 b2 -> b1 && not b2)
  let disjoint t1 t2 = assert false (*TODO*)
*)
  let to_seq t = Seq.map fst (M.to_seq t)
  let to_seq_from x t = Seq.map fst (M.to_seq_from x t)

  let add_seq s m =
    Seq.fold_left (fun m x -> add x m) m s

  let of_seq s =
    Seq.fold_left (fun m x -> add x m) empty s

end
