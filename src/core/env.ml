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

open Ident
open Theory

(** Environment *)

type env = {
  env_retrieve : retrieve_theory;
  env_memo     : (string list, theory Mnm.t) Hashtbl.t;
  env_tag      : int;
}

and retrieve_theory = env -> string list -> theory Mnm.t

let create_env =
  let r = ref 0 in
  fun retrieve ->
    incr r;
    let env = {
      env_retrieve = retrieve;
      env_memo     = Hashtbl.create 17;
      env_tag      = !r }
    in
    let th = builtin_theory in
    let m = Mnm.add th.th_name.id_short th Mnm.empty in
    Hashtbl.add env.env_memo [] m;
    env

exception TheoryNotFound of string list * string

let find_theory env sl s =
  try 
    let m =
      try
	Hashtbl.find env.env_memo sl
      with Not_found ->
	Hashtbl.add env.env_memo sl Mnm.empty;
	let m = env.env_retrieve env sl in
	Hashtbl.replace env.env_memo sl m;
	m
    in
    Mnm.find s m
  with Not_found -> 
    raise (TheoryNotFound (sl, s))

let env_tag env = env.env_tag

