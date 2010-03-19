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

type 'a value = env option -> clone option -> 'a

type 'a registered = {
  mutable value    : 'a value;
          generate : unit -> 'a value;
}

type 'a trans_reg = 'a trans registered
type 'a tlist_reg = 'a tlist registered

let create gen = {
  value    = gen ();
  generate = gen;
}

exception ArgumentNeeded

let memo f tag h = function
  | None -> raise ArgumentNeeded
  | Some x ->
      let t = tag x in
      try Hashtbl.find h t
      with Not_found ->
        let r = f x in
        Hashtbl.add h t r;
        r

let memo0 tag f = memo f tag (Hashtbl.create 7)

let unused0 f = fun _ -> f

let cl_tag cl = cl.cl_tag

let store0 memo_env memo_cl f =
  let gen () =
    let f2 = memo_env (f ()) in
    fun env -> memo_cl (f2 env)
  in
  create gen

let store       f = store0 unused0         unused0        f
let store_env   f = store0 (memo0 env_tag) unused0        f
let store_clone f = store0 (memo0 env_tag) (memo0 cl_tag) f

let apply0 reg env clone = Trans.apply (reg.value env clone)

let apply_clone reg env clone = apply0 reg (Some env) (Some clone)
let apply_env   reg env       = apply0 reg (Some env) None
let apply       reg           = apply0 reg None       None

let clear reg = reg.value <- reg.generate ()

let combine comb reg1 reg2 =
  let gen () =
    let reg1 = reg1.generate () in
    let reg2 = reg2.generate () in
    fun env cl -> comb (reg1 env cl) (reg2 env cl) in
  create gen

let compose   r1 r2 = combine (fun t1 t2 -> Trans.compose   t1 t2) r1 r2
let compose_l r1 r2 = combine (fun t1 t2 -> Trans.compose_l t1 t2) r1 r2

let conv_res conv reg1 =
  let gen () =
    let reg1 = reg1.generate () in
    fun env cl -> conv (reg1 env cl) in
  create gen

let singleton reg = conv_res Trans.singleton reg

let identity   = store (fun () -> Trans.identity)
let identity_l = store (fun () -> Trans.identity_l)

