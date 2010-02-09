(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Francois Bobot, Jean-Christophe Filliatre,              *)
(*  Johannes Kanig and Andrei Paskevich.                                  *)
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

type node = 
  | BVar of int
  | Var of Name.t
  | Tuple of t * t
  | Arrow of t * t
and t = {tag : int ; node : node }
and scheme = Name.t list * t

module Base = struct
  type node' = node 
  type node = node'
  type t' = t
  type t = t'

  let rec equal t1 t2 = 
    match t1, t2 with
    | Var n1, Var n2 -> Name.equal n1 n2
    | BVar (i1), BVar (i2) -> i1 = i2
    | Tuple (ta1, ta2), Tuple (tb1, tb2)
    | Arrow (ta1, ta2), Arrow (tb1, tb2) -> 
        equal_t ta1 tb1 && equal_t ta2 tb2
    | Var _, _ | _, Var _ -> false
    | BVar _, _ | _, BVar _ -> false
    | Tuple _, _ | _, Tuple _ -> false
  and equal_t t1 t2 = t1 == t2

  let node t = t.node

  open Misc

  let hash n = 
    match n with
    | BVar (i) -> combine 1 (hash_int i)
    | Var n -> combine 2 (Name.hash n)
    | Arrow (t1,t2) -> combine2 3 t1.tag t2.tag
    | Tuple (t1,t2) -> combine2 5 t1.tag t2.tag
end

let hc_equal = Base.equal_t
let hash t = t.tag

module HBase = Hashcons.Make (Base)

let mk_t n t = { tag = t; node = n }
let bvar i = HBase.hashcons (BVar (i)) mk_t
let var v = HBase.hashcons (Var v) mk_t
let tuple t1 t2 = HBase.hashcons (Tuple (t1,t2)) mk_t
let arrow t1 t2 = HBase.hashcons (Arrow (t1,t2)) mk_t

let map f t = 
  let rec aux t = 
    let t =
      match t.node with
      | Var _ | BVar _  -> t
      | Tuple (t1,t2) -> tuple (aux t1) (aux t2)
      | Arrow (t1,t2) -> arrow (aux t1) (aux t2) in
    f t in
  aux t

let abstract nl = 
  let m = Name.build_map nl in
  let f t = match t.node with
  | Var n -> 
      begin try let i = Name.M.find n m in bvar i
      with Not_found -> t end
  | _ -> t in
  map f

let instantiate tl =
  let f t = match t.node with
  | BVar i -> List.nth tl i
  | _ -> t in
  map f

open Format

let rec print tenv fmt t = 
  match t.node with
  | BVar i -> 
      begin try Name.print fmt (List.nth tenv i)
      with Invalid_argument "List.nth" -> Format.printf "{{%d}}" i end
  | Var n -> Name.print fmt n
  | Tuple (t1,t2) -> fprintf fmt "%a * %a" (print tenv) t1 (print tenv) t2
  | Arrow (t1,t2) -> fprintf fmt "%a -> %a" (print tenv) t1 (paren tenv) t2
and is_compound t = 
  match t.node with
  | Arrow _ -> true
  | BVar _ | Var _ | Tuple _ -> false
and paren tenv fmt t = 
  if is_compound t then fprintf fmt "(%a)" (print tenv) t 
  else print tenv fmt t

let equal a b = a == b

let open_ (nl,t) = 
  let tl = List.map var nl in
  nl, instantiate tl t 

let close nl t = 
  let nl' = List.map Name.fresh nl in
  nl', abstract nl t

let as_scheme t = [],t

let instantiate_scheme tl (_,t) = instantiate tl t 

let prop = var (Name.from_string "prop")

let split t = 
  match t.node with
  | Arrow (t1,t2) -> t1,t2
  | _ -> failwith "not an arrow"

let tuple_split t = 
  match t.node with
  | Tuple (t1,t2) -> t1,t2
  | _ -> failwith "not a tuple"
