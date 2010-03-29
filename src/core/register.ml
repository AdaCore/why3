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

open Env
open Task
open Trans

type 'a value = env option -> 'a

type 'a registered = {
  mutable value    : 'a value;
          generate : unit -> 'a value;
}

type 'a trans_reg = (task -> 'a) registered
type 'a tlist_reg = (task -> 'a list) registered

type use = Theory.use_map
type clone = Theory.clone_map

let create gen = {
  value    = gen ();
  generate = gen;
}

exception ArgumentNeeded

let memo tag f = 
  let h = Hashtbl.create 7 in
  function
  | None -> raise ArgumentNeeded
  | Some x ->
      let t = tag x in
      try Hashtbl.find h t
      with Not_found ->
        let r = f x in
        Hashtbl.add h t r;
        r

let memo_env e = memo env_tag e

let memo2 extract f =
  let h = Hashtbl.create 7 in
  fun x ->
    let arg,tag = extract x in
    try Hashtbl.find h tag
    with Not_found ->
      let r = f arg x in
      Hashtbl.add h tag r; r

let memo_clone x = memo2 (fun t -> 
                          let t = last_clone t in
                          task_clone t,task_tag t) x
let memo_use x = memo2 (fun t -> 
                          let t = last_use t in
                          task_used t,task_tag t) x

let memo_task x = memo2 (fun t -> t,task_tag t) x

let store f = 
  let gen () = 
    let f0 _ task = Trans.apply (f ()) task in
    f0 in
  create gen

let store0 memo_env f =
  let gen () = 
    let f0 () env task = Trans.apply (f () env) task in
    memo_env (f0 ()) in
  create gen


let store1 memo_env memo_arg2 f =
  let gen () =
    let f0 () env arg2 task = Trans.apply (f () env arg2) task in
    let f1 () env = memo_arg2 (f0 () env) in
    memo_env (f1 ()) in
  create gen


let store2 memo_env memo_arg2 memo_arg3 f =
  let gen () =
    let f0 () env arg2 arg3 task = Trans.apply (f () env arg2 arg3) task in
    let f1 () env arg2 = memo_arg3 (f0 () env arg2) in
    let f2 () env = memo_arg2 (f1 () env) in
    memo_env (f2 ()) in
  create gen


let store_env   f = store0 memo_env f
let store_clone f = store1 memo_env memo_clone f
let store_use   f = store1 memo_env memo_use   f
let store_task  f = store1 memo_env memo_task  f
let store_both  f = store2 memo_env memo_use   memo_clone f


let apply0 reg = reg.value

let apply_env   reg env       = apply0 reg (Some env)
let apply       reg           = apply0 reg None

let clear reg = reg.value <- reg.generate ()

let combine comb reg1 reg2 =
  let gen () =
    let reg1 = reg1.generate () in
    let reg2 = reg2.generate () in
    fun env -> comb (reg1 env) (reg2 env) in
  create gen

let compose   r1 r2 = combine (fun t1 t2 x -> t2 (t1 x)) r1 r2

let list_apply f = List.fold_left (fun acc x -> List.rev_append (f x) acc) []

let compose_l r1 r2 = combine (fun t1 t2 x -> list_apply t2 (t1 x)) r1 r2

let conv_res conv reg1 =
  let gen () =
    let reg1 = reg1.generate () in
    fun env -> conv (reg1 env) in
  create gen

let singleton reg = conv_res (fun f x -> [f x]) reg

let identity   = store (fun () -> Trans.identity)
let identity_l = store (fun () -> Trans.identity_l)

