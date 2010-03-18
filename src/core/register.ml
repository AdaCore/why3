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

type 'a registered = {mutable value : 'a value;
                      generate : unit -> 'a value;
                      tag : int}
let c = ref (-1)

let create gen =
  {value = gen ();
   generate = gen;
   tag = (incr c; !c)}

exception ArgumentNeeded


let memo f tag h  = function
  | None -> raise ArgumentNeeded
  | Some x ->
      let t = tag x in
      try
        Hashtbl.find h t
      with Not_found ->
        let r = f x in
        Hashtbl.add h t r;
        r
      
let store f = create (fun () -> 
                        let value = f () in
                        fun _ _ -> value)

let store_env f = 
  let f env = 
    let v = f env in
    fun cl -> v in
  let f () =
    let memo_t = Hashtbl.create 7 in
    memo f env_tag memo_t in
  create f
    
let cl_tag cl = cl.cl_tag

let store_clone f = 
  let f env =
    let memo_t = Hashtbl.create 7 in
    memo (f env) cl_tag memo_t in
  let f () =
    let memo_t = Hashtbl.create 7 in
    memo f env_tag memo_t in
  create f
      
let apply0 reg = reg.value
let apply_clone reg env clone = apply0 reg (Some env) (Some clone)
let apply_env reg env = apply0 reg (Some env) None
let apply reg = apply0 reg None None

let apply_trans0 reg env clone = Trans.apply (reg.value env clone)
let apply_trans_clone reg env clone = apply_trans0 reg (Some env) (Some clone)
let apply_trans_env reg env = apply_trans0 reg (Some env) None
let apply_trans reg = apply_trans0 reg None None


let clear reg = reg.value<-reg.generate ()
let clear_all () = assert false

let compose0 comp reg1 reg2 = 
  let gen () =
    let reg1 = reg1.generate () in
    let reg2 = reg2.generate () in
    fun env cl -> comp (reg1 env cl) (reg2 env cl) in
  create gen

let compose reg1 reg2 = compose0 (fun f g x -> g (f x)) reg1 reg2
let compose_trans reg1 reg2 = compose0 (fun f g -> Trans.compose f g) reg1 reg2
let compose_trans_l reg1 reg2 = compose0 (fun f g -> Trans.compose_l f g) 
  reg1 reg2
  
