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
open Theory
open Task

(** Task transformation *)

type 'a trans = task -> 'a
type 'a tlist = 'a list trans

let identity   x =  x
let identity_l x = [x]

let conv_res c f x = c (f x)

let singleton f x = [f x]

let compose   f g x =            g (f x)
let compose_l f g x = list_apply g (f x)

let apply f x = f x

module WHtask = Hashweak.Make (struct
  type t = task_hd
  let tag t = t.task_tag
end)

let store fn = WHtask.memoize_option 63 fn

let fold fn v =
  let h = WHtask.create 63 in
  let rewind acc task =
    let acc = fn task acc in
    WHtask.set h task acc;
    acc
  in
  let current task =
    try Some (WHtask.find h task)
    with Not_found -> None
  in
  let rec accum todo = function
    | None -> List.fold_left rewind v todo
    | Some task -> begin match current task with
        | Some v -> List.fold_left rewind v todo
        | None   -> accum (task::todo) task.task_prev
      end
  in
  accum []

let fold_l fn v = fold (fun task -> list_apply (fn task)) [v]

let fold_map   fn v t = conv_res snd                (fold   fn (v, t))
let fold_map_l fn v t = conv_res (List.rev_map snd) (fold_l fn (v, t))

let map   fn = fold   (fun t1 t2 -> fn t1 t2)
let map_l fn = fold_l (fun t1 t2 -> fn t1 t2)

module WHdecl = Hashweak.Make (struct
  type t = decl
  let tag d = d.d_tag
end)

let gen_decl add fn =
  let fn = WHdecl.memoize 63 fn in
  let fn task acc = match task.task_decl.td_node with
    | Decl d -> List.fold_left add acc (fn d)
    | _ -> add_tdecl acc task.task_decl
  in
  map fn

let gen_decl_l add fn =
  let fn = WHdecl.memoize 63 fn in
  let fn task acc = match task.task_decl.td_node with
    | Decl d -> List.rev_map (List.fold_left add acc) (fn d)
    | _ -> [add_tdecl acc task.task_decl]
  in
  map_l fn

let decl    = gen_decl   add_decl
let decl_l  = gen_decl_l add_decl
let tdecl   = gen_decl   add_tdecl
let tdecl_l = gen_decl_l add_tdecl

let rewrite fnT fnF = decl (fun d -> [decl_map fnT fnF d])

(** dependent transformations *)

module Wtds = Hashweak.Make (struct
  type t = tdecl_set
  let tag s = s.tds_tag
end)

let on_theory th fn =
  let fn = Wtds.memoize 17 fn in
  fun task -> fn (find_clone task th) task

let on_meta t fn =
  let fn = Wtds.memoize 17 fn in
  fun task -> fn (find_meta task t) task

let on_theories tl fn =
  let rec pass acc = function
    | th::tl -> on_theory th (fun st -> pass (Mid.add th.th_name st acc) tl)
    | []     -> fn acc
  in
  pass Mid.empty tl

let on_metas tl fn =
  let rec pass acc = function
    | t::tl -> on_meta t (fun st -> pass (Mstr.add t st acc) tl)
    | []    -> fn acc
  in
  pass Mstr.empty tl

let on_theories_metas thl tl fn =
  on_theories thl (fun cm -> on_metas tl (fn cm))

(** register transformations *)

open Env

module Wenv = Hashweak.Make (struct
  type t = env
  let tag = env_tag
end)

exception UnknownTrans of string
exception KnownTrans of string

let transforms   : (string, env -> task trans) Hashtbl.t = Hashtbl.create 17
let transforms_l : (string, env -> task tlist) Hashtbl.t = Hashtbl.create 17

let register_transform s p =
  if Hashtbl.mem transforms s then raise (KnownTrans s);
  Hashtbl.replace transforms s (Wenv.memoize 3 p)

let register_transform_l s p =
  if Hashtbl.mem transforms_l s then raise (KnownTrans s);
  Hashtbl.replace transforms_l s (Wenv.memoize 3 p)

let lookup_transform s =
  try Hashtbl.find transforms s with Not_found -> raise (UnknownTrans s)

let lookup_transform_l s =
  try Hashtbl.find transforms_l s with Not_found -> raise (UnknownTrans s)

let list_transforms ()   = Hashtbl.fold (fun k _ acc -> k::acc) transforms []
let list_transforms_l () = Hashtbl.fold (fun k _ acc -> k::acc) transforms_l []

let () = Exn_printer.register (fun fmt exn -> match exn with
  | KnownTrans s ->
      Format.fprintf fmt "Transformation '%s' is already registered" s
  | UnknownTrans s ->
      Format.fprintf fmt "Unknown transformation '%s'" s
  | e -> raise e)

