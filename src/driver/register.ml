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

open Task
open Trans
open Driver

type use   = Theory.use_map
type clone = Theory.clone_map
type query = driver_query

type 'a value = Env.env option -> driver option -> task -> 'a

type 'a trans_reg = {
  mutable value    : 'a value;
          generate : unit -> 'a value;
}

type 'a tlist_reg = 'a list trans_reg

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

let memo_env e   = memo Env.env_tag e
let memo_query q = memo query_tag q

let memo2 extract f =
  let h = Hashtbl.create 7 in
  fun x ->
    let arg,tag = extract x in
    try Hashtbl.find h tag
    with Not_found ->
      let r = f arg x in
      Hashtbl.add h tag r; r

let memo_use x   = memo2 (fun t -> task_used t,  task_tag (last_use   t)) x
let memo_clone x = memo2 (fun t -> task_clone t, task_tag (last_clone t)) x
let memo_goal x  = memo2 (fun t -> t, task_tag t) x

let query drv task = Util.option_map (fun d -> driver_query d task) drv

let gen_gen f () =
  let f0 = Trans.apply (f ()) in
  fun _ _ -> f0

let gen_env f () =
  let f0 env = Trans.apply (f env) in
  let f1 = memo_env f0 in
  fun env _ -> f1 env

let gen_query f () =
  let f0 query = Trans.apply (f query) in
  let f1 = memo_query f0 in
  fun _ drv task -> f1 (query drv task) task

let gen_arg memo_arg f () =
  let f0 env arg = Trans.apply (f env arg) in
  let f1 env = memo_arg (f0 env) in
  let f2 = memo_env f1 in
  fun env _ -> f2 env

let gen_full f () =
  let f0 query goal = Trans.apply (f query goal) in
  let f1 query = memo_goal (f0 query) in
  let f2 = memo_query f1 in
  fun _ drv task -> f2 (query drv task) task

let gen_both f () =
  let f0 env use clone = Trans.apply (f env use clone) in
  let f1 env use = memo_clone (f0 env use) in
  let f2 env = memo_use (f1 env) in
  let f3 = memo_env f2 in
  fun env _ -> f3 env

let store       f = create (gen_gen f)
let store_env   f = create (gen_env f)
let store_goal  f = create (gen_arg memo_goal f)
let store_clone f = create (gen_arg memo_clone f)
let store_use   f = create (gen_arg memo_use f)
let store_both  f = create (gen_both f)
let store_query f = create (gen_query f)
let store_full  f = create (gen_full f)

let apply reg = reg.value None None
let apply_env reg env = reg.value (Some env) None
let apply_driver reg drv = reg.value (Some (get_env drv)) (Some drv)

let clear reg = reg.value <- reg.generate ()

let conv_res conv reg1 =
  let app f env drv task = conv (f env drv task) in
  let gen () = app (reg1.generate ()) in
  { value = app reg1.value; generate = gen }

let combine comb reg1 reg2 =
  let app f1 f2 env drv = comb (f1 env drv) (f2 env drv) in
  let gen () = app (reg1.generate ()) (reg2.generate ()) in
  { value = app reg1.value reg2.value; generate = gen }

let singleton reg = conv_res (fun x -> [x]) reg

let identity   = store (fun () -> Trans.identity)
let identity_l = store (fun () -> Trans.identity_l)

let compose   r1 r2 = combine (fun t1 t2 x -> t2 (t1 x)) r1 r2
let compose_l r1 r2 = combine (fun t1 t2 x -> Util.list_apply t2 (t1 x)) r1 r2

(** register printers and transformations *)

type printer = query -> Format.formatter -> task -> unit

let printers     : (string, printer)        Hashtbl.t = Hashtbl.create 17
let transforms   : (string, task trans_reg) Hashtbl.t = Hashtbl.create 17
let transforms_l : (string, task tlist_reg) Hashtbl.t = Hashtbl.create 17

let register_printer     = Hashtbl.replace printers
let register_transform   = Hashtbl.replace transforms
let register_transform_l = Hashtbl.replace transforms_l

let lookup_printer       = Hashtbl.find printers
let lookup_transform     = Hashtbl.find transforms
let lookup_transform_l   = Hashtbl.find transforms_l

let list_printers ()     = Hashtbl.fold (fun k _ acc -> k::acc) printers []
let list_transforms ()   = Hashtbl.fold (fun k _ acc -> k::acc) transforms []
let list_transforms_l () = Hashtbl.fold (fun k _ acc -> k::acc) transforms_l []

