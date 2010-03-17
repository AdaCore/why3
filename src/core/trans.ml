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

open Util
open Ident
open Ty
open Term
open Decl
open Task

(** Task transformation *)

type 'a trans = task -> 'a
type 'a tlist = 'a list trans

let identity   x = x
let identity_l x = [x]

let conv_res f c x = c (f x)

let singleton f x = [f x]

let compose f g x = g (f x)

let list_apply f = List.fold_left (fun acc x -> List.rev_append (f x) acc) []

let compose_l f g x = list_apply g (f x)

let apply f x = f x

let ymemo f tag h =
  let rec aux x =
    let t = tag x in
    try
      Hashtbl.find h t
    with Not_found ->
      let r = f aux x in
      Hashtbl.add h t r;
      r in
  aux

let memo f tag h = ymemo (fun _ -> f) tag h

let term_tag t = t.t_tag
let fmla_tag f = f.f_tag
let decl_tag d = d.d_tag

let task_tag = function
  | Some t -> t.task_tag
  | None   -> -1

let store f = memo f task_tag (Hashtbl.create 63)

let accum memo_t rewind v =
  let rec accum todo = function
    | Some task ->
        let curr =
          try Some (Hashtbl.find memo_t task.task_tag)
          with Not_found -> None
        in
        begin match curr with
          | Some curr -> rewind curr todo
          | None      -> accum (task::todo) task.task_prev
        end
    | None -> rewind v todo
  in
  accum

let save memo_t task v = Hashtbl.add memo_t task.task_tag v; v

let fold fn v =
  let memo_t = Hashtbl.create 63 in
  let rewind x task = save memo_t task (fn task x) in
  let rewind = List.fold_left rewind in
  accum memo_t rewind v []

let fold_l fn v =
  let memo_t = Hashtbl.create 63 in
  let rewind x task = save memo_t task (list_apply (fn task) x) in
  let rewind = List.fold_left rewind in
  accum memo_t rewind [v] []

let fold_map   fn v t = conv_res (fold   fn (v, t)) snd
let fold_map_l fn v t = conv_res (fold_l fn (v, t)) (List.rev_map snd)

let map   fn = fold   (fun t1 t2 -> fn t1 t2)
let map_l fn = fold_l (fun t1 t2 -> fn t1 t2)

let decl fn =
  let memo_t = Hashtbl.create 63 in
  let fn task = memo fn decl_tag memo_t task.task_decl in
  let fn task acc = List.fold_left add_decl acc (fn task) in
  map fn

let decl_l fn =
  let memo_t = Hashtbl.create 63 in
  let fn task = memo fn decl_tag memo_t task.task_decl in
  let fn task acc = List.rev_map (List.fold_left add_decl acc) (fn task) in
  map_l fn

let rewrite fnT fnF d = match d.d_node with
  | Dtype _ ->
      d
  | Dlogic l ->
      let fn = function
        | ls, Some ld ->
            let vl,e = open_ls_defn ld in
            make_ls_defn ls vl (e_map fnT fnF e)
        | ld -> ld
      in
      create_logic_decl (List.map fn l)
  | Dind l ->
      let fn (pr,f) = pr, fnF f in
      let fn (ps,l) = ps, List.map fn l in
      create_ind_decl (List.map fn l)
  | Dprop (k,pr,f) ->
      create_prop_decl k pr (fnF f)

let expr fnT fnF = decl (fun d -> [rewrite fnT fnF d])

