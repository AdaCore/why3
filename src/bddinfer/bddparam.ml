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

(* open Why3 *)
(* to comment out when inside Why3 *)

(** {1 Parametric Binary Decision Diagrams} *)

type variable = int (* 1..max_var *)

module BddVarMap =
  Map.Make(struct
      type t = variable
      let compare (x:variable) (y:variable) = compare x y
    end)

module type BDD = sig
  val get_max_var : unit -> int
  type t
  type param_index = int
  type param_context
  (* type param_constraint *)
  type param_state
  type formula =
    | Ffalse
    | Ftrue
    | Fstate of param_index
    | Fvar of variable
    | Fand of formula * formula
    | For  of formula * formula
    | Fimp of formula * formula
    | Fiff of formula * formula
    | Fnot of formula
    | Fite of formula * formula * formula (* if f1 then f2 else f3 *)

  val bottom : t
  val top : t
  val make : variable -> low:t -> high:t -> t
  val mk_var : variable -> t
  val mk_param : param_index -> t
  val mk_not : param_context -> t -> t
  val meet : param_context -> t -> t -> t
  val join : param_context -> t -> t -> t
  val widening : param_context -> t -> t -> t
  (* val mk_eq_var : variable -> variable -> t *)
  val change_ctx :
    (param_state -> param_state) ->
    param_context -> t -> param_context -> t
  val rename_many :
    (variable -> variable) ->
    (param_state -> param_state) ->
    param_context -> t -> param_context -> t
  val rename_few :
    (variable * variable) list ->
    (param_state -> param_state) ->
    param_context -> t -> param_context -> t
  val meet_with_param_constraint :
    (param_state -> param_state) ->
    param_context -> t -> t
  val mk_exist : (variable -> bool) -> param_context -> t -> param_context -> t
  val extract_known_values : t -> bool BddVarMap.t
  val fold_param_states : (bool -> 'a -> 'a) -> (param_index -> 'a -> 'a) -> t -> 'a -> 'a
  val as_formula : t -> formula
  val as_compact_formula : param_context -> t -> formula
  val is_sat : t -> bool
  val is_top : t -> bool
  val is_bottom : t -> bool
  val equivalent : t -> t -> bool
  val entails : param_context -> t -> t -> bool


  val print_var : Format.formatter -> variable -> unit
  val print : Format.formatter -> t -> unit
  val print_compact : Format.formatter -> t -> unit
  val stats : unit -> (int * int * int * int * int * int) array
end

let debug = false

(* Make a fresh module *)

module type VarSig = sig
  val print_var: Format.formatter -> int -> unit
  val size: int
  val max_var: int
end

module type ParamDomain = sig
  type param_index = int
  type param_context
  type param_state
  val meet : param_context -> param_index -> param_index -> param_index option
  val join : param_context -> param_index -> param_index -> param_index option
  val widening : param_context -> param_index -> param_index -> param_index option
  val exist_elim : param_context -> param_index -> param_context -> param_index option
  val entails : param_context -> param_index -> param_index -> bool
  val change :
    (param_state -> param_state) ->
    param_context -> param_index -> param_context -> param_index
  val meet_with_constraint :
    (param_state -> param_state) ->
    param_context -> param_index option -> param_index option
end

module Make (D: ParamDomain) (X: VarSig) = struct
  open X

let rec power_2_above x n =
  if x >= n then x
  else if x * 2 > Sys.max_array_length then x
  else power_2_above (x * 2) n

let size = power_2_above 16 size

let print_var = print_var

let get_max_var () = max_var

type bdd = { tag: int; node : view }
and view = Zero | One | Leaf of int | Node of variable * bdd (*low*) * bdd (*high*)

let smaller_var v b = match b.node with
  | Zero | One | Leaf _ -> true
  | Node (w, _, _) -> v < w


type t = bdd (* export *)

(*
let view b = b.node
*)

let rec print fmt b =
  match b.node with
  | Zero -> Format.fprintf fmt "false"
  | One  -> Format.fprintf fmt "true"
  | Leaf n  -> Format.fprintf fmt "F(%d)" n
  | Node(v,l,h) ->
     Format.fprintf fmt "@[<hv 2>if %a@ then %a@ else %a@]" print_var v print h print l

let rec print_compact fmt b =
  match b.node with
  | Zero -> Format.fprintf fmt "false"
  | One  -> Format.fprintf fmt "true"
  | Leaf n  -> Format.fprintf fmt "F(%d)" n
  | Node(v,{node=Zero;_},{node=One;_}) ->
     (* if v then 1 else 0 --> v *)
     Format.fprintf fmt "%a" print_var v
  | Node(v,{node=One;_},{node=Zero;_}) ->
     (* if v then 0 else 1 --> !v *)
     Format.fprintf fmt "!%a" print_var v
  | Node(v,{node=Zero;_},h) ->
     (* if v then h else 0 --> v /\ h *)
     Format.fprintf fmt "@[%a /\\@ %a@]" print_var v print_compact h
  | Node(v,{node=One;_},h) ->
     (* if v then h else 1 --> !v \/ h *)
     Format.fprintf fmt "@[!%a \\/@ %a@]" print_var v print_compact h
  | Node(v,l,{node=Zero;_}) ->
     (* if v then 0 else l --> !v /\ l *)
     Format.fprintf fmt "@[!%a /\\@ %a@]" print_var v print_compact l
  | Node(v,l,{node=One;_}) ->
     (* if v then 1 else l --> v \/ l *)
     Format.fprintf fmt "@[%a \\/@ %a@]" print_var v print_compact l
  | Node(v,l,h) ->
     Format.fprintf fmt "@[<hv 2>if %a@ then %a@ else %a@]" print_var v print_compact h print_compact l


let hash_node l h = 19 * l.tag + h.tag

let hash = function
  | Zero -> 0
  | One -> 1
  | Leaf n -> n+2
  | Node (_, l, h) -> hash_node l h

let gentag = let r = ref (-1) in fun () -> incr r; !r

type table = {
  mutable table : bdd Weak.t array;
  mutable totsize : int;             (* sum of the bucket sizes *)
  mutable limit : int;               (* max ratio totsize/table length *)
}

let create sz =
  let emptybucket = Weak.create 0 in
  { table = Array.make sz emptybucket;
    totsize = 0;
    limit = 3; }

let vt = Array.init max_var (fun _ -> create size)

let fold f t init =
  let rec fold_bucket i b accu =
    if i >= Weak.length b then accu else
      match Weak.get b i with
        | Some v -> fold_bucket (i+1) b (f v accu)
        | None -> fold_bucket (i+1) b accu
  in
  Array.fold_right (fold_bucket 0) t.table init


let count t =
  let rec count_bucket i b accu =
    if i >= Weak.length b then accu else
      count_bucket (i+1) b (accu + (if Weak.check b i then 1 else 0))
  in
  Array.fold_right (count_bucket 0) t.table 0

let rec resize t =
  if debug then Format.eprintf "resizing...@.";
  let oldlen = Array.length t.table in
  let newlen = oldlen * 2 in
  if newlen > oldlen then begin
    let newt = create newlen in
    newt.limit <- t.limit + 100;          (* prevent resizing of newt *)
    fold (fun d () -> add newt d) t ();
    t.table <- newt.table;
    t.limit <- t.limit + 2;
  end

and add t d =
  add_index t d ((hash d.node) land (Array.length t.table - 1))

and add_index t d index =
  let bucket = t.table.(index) in
  let sz = Weak.length bucket in
  let rec loop i =
    if i >= sz then begin
      let newsz = min (sz + 3) (Sys.max_array_length - 1) in
      if newsz <= sz then
        failwith "Hashcons.Make: hash bucket cannot grow more";
      let newbucket = Weak.create newsz in
      Weak.blit bucket 0 newbucket 0 sz;
      Weak.set newbucket i (Some d);
      t.table.(index) <- newbucket;
      t.totsize <- t.totsize + (newsz - sz);
      if t.totsize > t.limit * Array.length t.table then resize t;
    end else begin
      if Weak.check bucket i
      then loop (i+1)
      else Weak.set bucket i (Some d)
    end
  in
  loop 0

let hashcons_node v l h =
  let t = vt.(v - 1) in
  let index = (hash_node l h) mod (Array.length t.table) in
  let bucket = t.table.(index) in
  let sz = Weak.length bucket in
  let rec loop i =
    if i >= sz then begin
      let hnode = { tag = gentag (); node = Node (v, l, h) } in
      add_index t hnode index;
      hnode
    end else begin
      match Weak.get_copy bucket i with
        | Some {node=Node(v',l',h'); _} when v==v' && l==l' && h==h' ->
            begin match Weak.get bucket i with
              | Some v -> v
              | None -> loop (i+1)
            end
        | _ -> loop (i+1)
    end
  in
  loop 0

let stat t =
  let len = Array.length t.table in
  let lens = Array.map Weak.length t.table in
  Array.sort compare lens;
  let totlen = Array.fold_left ( + ) 0 lens in
  (len, count t, totlen, lens.(0), lens.(len/2), lens.(len-1))

let stats () = Array.map stat vt

(* zero and one allocated once and for all *)
let zero = { tag = gentag (); node = Zero }
let one = { tag = gentag (); node = One }

let bottom = zero
let top = one

let mk v ~low ~high =
  if low == high then low else hashcons_node v low high

let make v ~low ~high =
  if v < 1 || v > max_var then invalid_arg "Bdd.make";
  mk v ~low ~high

let mk_var v =
  if v < 1 || v > max_var then invalid_arg "Bdd.mk_var";
  mk v ~low:zero ~high:one

let mk_not_var v =
  if v < 1 || v > max_var then invalid_arg "Bdd.mk_not_var";
  mk v ~low:one ~high:zero

module Hint = Wstdlib.Hint

type param_index = int

type param_context = D.param_context

type param_state = D.param_state

let param_table = Hint.create 17

let mk_param (i : param_index) : t =
  try
    Hint.find param_table i
  with Not_found ->
    let t = gentag () in
    let n = { tag = t; node = Leaf i } in
    Hint.add param_table i n;
    n

module Bdd = struct
  type t = bdd
  let equal = (==)
  let hash b = b.tag
  (* let compare b1 b2 = Stdlib.compare b1.tag b2.tag *)
end

module H1 = Hashtbl.Make(Bdd)

let cache_default_size = 7001

let mk_not ctx x =
  let cache = H1.create cache_default_size in
  let rec mk_not_rec x =
    try
      H1.find cache x
    with Not_found ->
      let res = match x.node with
        | Zero -> one
        | One -> zero
        | Leaf _ -> ignore ctx; assert false (* TODO *)
        | Node (v, l, h) -> mk v ~low:(mk_not_rec l) ~high:(mk_not_rec h)
      in
      H1.add cache x res;
      res
  in
  mk_not_rec x


module H2 = Hashtbl.Make(
  struct
    type t = bdd * bdd
    let equal (u1,v1) (u2,v2) = u1==u2 && v1==v2
    let hash (u,v) =
      (*abs (19 * u.tag + v.tag)*)
      let s = u.tag + v.tag in abs (s * (s+1) / 2 + u.tag)
  end)



let meet ctx b1 b2 =
  let cache = H2.create cache_default_size in
  let rec app ((u1,u2) as u12) =
    if u1 == u2 then u1 else
      match u1.node, u2.node with
      | Zero,_ | _, Zero -> zero
      | One,_ -> u2
      | _, One -> u1
      | _ ->
        try
          H2.find cache u12
        with Not_found ->
          let res =
            match u1.node,u2.node with
            | Node(v1,l1,h1), Node(v2,l2,h2) ->
              if v1 == v2 then
                mk v1 ~low:(app (l1, l2)) ~high:(app (h1, h2))
              else if v1 < v2 then
                mk v1 ~low:(app (l1, u2)) ~high:(app (h1, u2))
              else (* v1 > v2 *)
                mk v2 ~low:(app (u1, l2)) ~high:(app (u1, h2))
            | Leaf i, Leaf j ->
              begin
                match D.meet ctx i j with
                | Some k -> mk_param k
                | None -> zero
              end
            | Node(v1,l1,h1), Leaf _ ->
                mk v1 ~low:(app (l1, u2)) ~high:(app (h1, u2))
            | Leaf _,Node(v2,l2,h2) ->
              mk v2 ~low:(app (u1, l2)) ~high:(app (u1, h2))
            | (Zero|One),_ | _,(Zero|One) -> assert false
          in
          H2.add cache u12 res;
          res
    in
    app (b1, b2)


let generic_or op ctx b1 b2 =
  let cache = H2.create cache_default_size in
  let rec app ((u1,u2) as u12) =
    if u1 == u2 then u1 else
      match u1.node, u2.node with
      | One,_ | _, One -> one
      | Zero,_ -> u2
      | _, Zero -> u1
      | _ ->
        try
          H2.find cache u12
        with Not_found ->
          let res =
            match u1.node,u2.node with
            | Node(v1,l1,h1), Node(v2,l2,h2) ->
              if v1 == v2 then
                mk v1 ~low:(app (l1, l2)) ~high:(app (h1, h2))
              else if v1 < v2 then
                mk v1 ~low:(app (l1, u2)) ~high:(app (h1, u2))
              else (* v1 > v2 *)
                mk v2 ~low:(app (u1, l2)) ~high:(app (u1, h2))
            | Leaf i, Leaf j ->
              begin
                match op ctx i j with
                | Some k -> mk_param k
                | None -> one
              end
            | Node(v1,l1,h1), Leaf _ ->
                mk v1 ~low:(app (l1, u2)) ~high:(app (h1, u2))
            | Leaf _,Node(v2,l2,h2) ->
              mk v2 ~low:(app (u1, l2)) ~high:(app (u1, h2))
            | (Zero|One),_ | _,(Zero|One) -> assert false
          in
          H2.add cache u12 res;
          res
    in
    app (b1, b2)

let join = generic_or D.join

let widening = generic_or D.widening


(* change context *)


let rec change_ctx_rec cache f ctx_src b ctx =
  match b.node with
  | One | Zero -> b
  | _ ->
    try
      H1.find cache b
    with Not_found ->
      let res =
        match b.node with
        | One | Zero -> assert false
        | Leaf i ->
          let j = D.change f ctx_src i ctx in
          mk_param j
        | Node(v,l,h) ->
          let low = change_ctx_rec cache f ctx_src l ctx in
          let high = change_ctx_rec cache f ctx_src h ctx in
          mk v ~low ~high
      in
      H1.add cache b res;
      res

let change_ctx f ctx_src b ctx =
  let cache = H1.create cache_default_size in
  change_ctx_rec cache f ctx_src b ctx



(** {2 quantifier elimination} *)

let rec quantifier_elim ~bddonly cache op filter ctxb b ctx =
  try
    H1.find cache b
  with Not_found ->
    let res = match b.node with
      | Zero | One -> b
      | Leaf i ->
        if bddonly then b else
        begin
          match D.exist_elim ctxb i ctx with
          | Some k -> mk_param k
          | None -> one
        end
      | Node(v,l,h) ->
         let low = quantifier_elim ~bddonly cache op filter ctxb l ctx in
         let high = quantifier_elim ~bddonly cache op filter ctxb h ctx in
         if filter v then
           op low high
         else
           mk v ~low ~high
    in
    H1.add cache b res;
    res


let mk_exist filter ctxb b ctx =
  let cache = H1.create cache_default_size in
  quantifier_elim ~bddonly:false cache (join ctx) filter ctxb b ctx

let mk_exist_bdd_only filter ctx b =
  let cache = H1.create cache_default_size in
  quantifier_elim ~bddonly:true cache (join ctx) filter ctx b ctx



(** renaming *)

let rec rename_many_rec cache rename_var rename_param ctxb b ctx =
  match b.node with
  | One | Zero -> b
  | _ ->
    try
      H1.find cache b
    with Not_found ->
      let res =
        match b.node with
        | One | Zero -> assert false
        | Leaf i ->
          let j = D.change rename_param ctxb i ctx in
          mk_param j
        | Node(v,l,h) ->
          let l = rename_many_rec cache rename_var rename_param ctxb l ctx in
          let h = rename_many_rec cache rename_var rename_param ctxb h ctx in
          let w = rename_var v in
          (* Format.eprintf "[renaming bvar %d into %d@." v w; *)
          if smaller_var w l && smaller_var w h then
            mk w ~low:l ~high:h
          else
            let mkv = mk_var w in
            let mknv = mk_not_var w in
            join ctx (meet ctx mknv l) (meet ctx mkv h)
      in
      H1.add cache b res;
      res

let rename_many rename_var rename_param ctxb b ctx =
  let cache = H1.create cache_default_size in
  rename_many_rec cache rename_var rename_param ctxb b ctx

let eq_var ctx v1 v2 =
  let mkv1 = mk_var v1 in
  let mkv2 = mk_var v2 in
  let mknv1 = mk_not_var v1 in
  let mknv2 = mk_not_var v2 in
  join ctx (meet ctx mkv1 mkv2) (meet ctx mknv1 mknv2)

let rename_few bool_renamings rename_param ctxb b ctx =
  (* first rename the parameter states *)
  let b = change_ctx rename_param ctxb b ctx in
  (* then build the BDD for variable equalities *)
  let br,s =
    List.fold_left
      (fun (acc,s) (v1,v2) -> (meet ctx acc (eq_var ctx v1 v2),BddVarMap.add v1 true s))
      (top,BddVarMap.empty)
      bool_renamings
  in
  (* build the conjunction *)
  let b = meet ctx b br in
  (* then eliminate variables *)
  let filter v =
    try BddVarMap.find v s with Not_found -> false
  in
  mk_exist_bdd_only filter ctx b

(** meet with a constraint in the parameter domain *)

let rec meet_with_rec cache meet_with ctxb b =
  match b.node with
  | Zero -> b
  | _ ->
    try
      H1.find cache b
    with Not_found ->
      let res =
        match b.node with
        | Zero -> assert false
        | One ->
          begin
            match D.meet_with_constraint meet_with ctxb None with
            | None -> zero
            | Some j -> mk_param j
          end
        | Leaf i ->
          begin
            match D.meet_with_constraint meet_with ctxb (Some i) with
            | None -> zero
            | Some j -> mk_param j
          end
        | Node(v,l,h) ->
          let l = meet_with_rec cache meet_with ctxb l in
          let h = meet_with_rec cache meet_with ctxb h in
          mk v ~low:l ~high:h
      in
      H1.add cache b res;
      res

let meet_with_param_constraint meet_with ctxb b =
  let cache = H1.create cache_default_size in
  meet_with_rec cache meet_with ctxb b

let rec extract_known_values cache b =
  try
    H1.find cache b
  with Not_found ->
    let res = match b.node with
      | Zero | One | Leaf _ -> BddVarMap.empty
      | Node(v,{node=Zero;_},h) ->
         (* if v then h else 0 --> v /\ h *)
         BddVarMap.add v true (extract_known_values cache h)
      | Node(v,l,{node=Zero;_}) ->
         (* if v then 0 else l --> !v /\ l *)
         BddVarMap.add v false (extract_known_values cache l)
      | Node(_,l,h) ->
         let m1 = extract_known_values cache l in
         let m2 = extract_known_values cache h in
         let merge_bool _ b1 b2 =
           match b1, b2 with
           | Some b1, Some b2 when b1=b2 -> Some b1
           | _ -> None
         in
         BddVarMap.merge merge_bool m1 m2
    in
    H1.add cache b res;
    res

let extract_known_values b =
  let cache = H1.create cache_default_size in
  extract_known_values cache b




let rec fold_param_states_rec cache f0 f b acc =
  try
    let _ = H1.find cache b in
    acc
  with Not_found ->
    H1.add cache b ();
    match b.node with
    | Leaf i -> f i acc
    | Zero -> f0 false acc
    | One -> f0 true acc
    | Node(_,l,h) ->
      let acc = fold_param_states_rec cache f0 f l acc in
      fold_param_states_rec cache f0 f h acc


let fold_param_states f0 f b acc =
  let cache = H1.create cache_default_size in
  fold_param_states_rec cache f0 f b acc







(* formula -> bdd *)

  type formula =
    | Ffalse
    | Ftrue
    | Fstate of param_index
    | Fvar of variable
    | Fand of formula * formula
    | For  of formula * formula
    | Fimp of formula * formula
    | Fiff of formula * formula
    | Fnot of formula
    | Fite of formula * formula * formula (* if f1 then f2 else f3 *)



let rec as_formula b =
  match b.node with
  | Zero -> Ffalse
  | One  -> Ftrue
  | Leaf i -> Fstate i
  | Node(v,l,h) -> Fite (Fvar v, as_formula h, as_formula l)

let rec as_compact_formula ctx b =
  match b.node with
  | Zero -> Ffalse
  | One  -> Ftrue
  | Leaf i -> Fstate i
  | Node(v,{node=Zero;_},{node=One;_}) ->
     (* if v then 1 else 0 --> v *)
     Fvar v
  | Node(v,{node=One;_},{node=Zero;_}) ->
     (* if v then 0 else 1 --> !v *)
     Fnot (Fvar v)
  | Node(v,{node=Zero;_},h) ->
     (* if v then h else 0 --> v /\ h *)
     Fand (Fvar v, as_compact_formula ctx h)
  | Node(v,{node=One;_},h) ->
     (* if v then h else 1 --> !v \/ h *)
     For (Fnot (Fvar v), as_compact_formula ctx h)
  | Node(v,l,{node=Zero;_}) ->
     (* if v then 0 else l --> !v /\ l *)
     Fand (Fnot (Fvar v), as_compact_formula ctx l)
  | Node(v,l,{node=One;_}) ->
     (* if v then 1 else l --> v \/ l *)
     For (Fvar v, as_compact_formula ctx l)
  | Node(v,l,h) ->
     Fite (Fvar v, as_compact_formula ctx h, as_compact_formula ctx l)

let mk_Fand f1 f2 =
  match f2 with
  | Ftrue -> f1
  | _ -> Fand(f1,f2)

let as_compact_formula ctx b =
  let m = extract_known_values b in
  let reduced_bdd =
    mk_exist_bdd_only (fun v ->
        try let _ = BddVarMap.find v m in true
        with Not_found -> false) ctx b
  in
  let f = as_compact_formula ctx reduced_bdd in
  BddVarMap.fold
    (fun v b f ->
      mk_Fand (if b then Fvar v else Fnot(Fvar v)) f )
    m f

(* satisfiability *)

let is_sat b = b.node != Zero

let is_bottom b = b.node == Zero

let is_top b = b.node == One

let equivalent b1 b2 = b1 == b2

let rec entails_rec cache ctx b1 b2 =
  match (b1.node, b2.node) with
  | Zero, _ -> true
  | _, One  -> true
  | One, _ -> false (* only b2=one would fit *)
  | _, Zero -> false (* only b1=zero would fit *)
  | _ ->
    try
      H2.find cache (b1,b2)
    with Not_found ->
      let res =
        match b1.node,b2.node with
        | Node(v1,l1,h1), Node(v2,l2,h2) ->
          if v1 == v2 then
            entails_rec cache ctx l1 l2 && entails_rec cache ctx h1 h2
          else if v1 < v2 then
            entails_rec cache ctx l1 b2 && entails_rec cache ctx h1 b2
          else (* v1 > v2 *)
            entails_rec cache ctx b1 l2 && entails_rec cache ctx b1 h2
        | Leaf i, Leaf j -> D.entails ctx i j
        | Node(_v1,l1,h1), Leaf _ ->
            entails_rec cache ctx l1 b2 && entails_rec cache ctx h1 b2
        | Leaf _,Node(_v2,l2,h2) ->
            entails_rec cache ctx b1 l2 && entails_rec cache ctx b1 h2
        | (Zero|One),_ | _,(Zero|One) -> assert false
      in
      H2.add cache (b1,b2) res;
      res

let entails ctx b1 b2 =
  let cache = H2.create cache_default_size in
  entails_rec cache ctx b1 b2


end (* module Make *)
