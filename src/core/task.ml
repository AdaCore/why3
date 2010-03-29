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

(** Task *)

type task = task_hd option

and task_hd = {
  task_decl  : tdecl;       (* last declaration *)
  task_prev  : task;        (* context *)
  task_known : known_map;   (* known identifiers *)
  task_clone : clone_map;   (* cloning history *)
  task_used  : use_map;     (* referenced theories *)
  task_tag   : int;         (* unique task tag *)
}

module Task = struct
  type t = task_hd

  let equal_pair (il1,ir1) (il2,ir2) = il1 == il2 && ir1 == ir2

  let equal_tdecl td1 td2 = match td1,td2 with
    | Decl d1, Decl d2 -> d1 == d2
    | Use th1, Use th2 -> th1.th_name == th2.th_name
    | Clone (th1,sl1), Clone (th2,sl2) ->
        th1.th_name == th2.th_name && list_all2 equal_pair sl1 sl2
    | _,_ -> false

  let equal a b =
    equal_tdecl a.task_decl b.task_decl &&
    match a.task_prev, b.task_prev with
      | Some na, Some nb -> na == nb
      | None, None -> true
      | _ -> false

  let hash_pair (il,ir) = Hashcons.combine il.id_tag ir.id_tag

  let hash_tdecl = function
    | Decl d -> Hashcons.combine 3 d.d_tag
    | Use th -> Hashcons.combine 5 th.th_name.id_tag
    | Clone (th,i) ->
        Hashcons.combine_list hash_pair th.th_name.id_tag i

  let hash task =
    let decl = hash_tdecl task.task_decl in
    let prev = match task.task_prev with
      | Some task -> 1 + task.task_tag
      | None -> 0
    in
    Hashcons.combine decl prev

  let tag i task = { task with task_tag = i }
end
module Htask = Hashcons.Make(Task)

let mk_task decl prev known clone used = Some (Htask.hashcons {
  task_decl  = decl;
  task_prev  = prev;
  task_known = known;
  task_clone = clone;
  task_used  = used;
  task_tag   = -1;
})

exception LemmaFound
exception GoalFound

let add_tdecl task td =
  let kn,cl,us = match task with
    | Some {task_decl=Decl{d_node=Dprop(Pgoal,_,_)}} -> raise GoalFound
    | Some task -> task.task_known, task.task_clone, task.task_used
    | None -> Mid.empty, Mid.empty, Mid.empty
  in
  match td with
    | Decl { d_node = Dprop (Plemma,_,_) } -> raise LemmaFound
    | Decl d ->
        begin try mk_task td task (known_add_decl kn d) cl us
        with KnownIdent _ -> task end
    | Use th ->
        if Mid.mem th.th_name us then task else
        mk_task td task kn cl (merge_used us th)
    | Clone (th,sl) ->
        mk_task td task kn (merge_clone cl th sl) us

let add_decl task d = add_tdecl task (Decl d)

(* declaration constructors + add_decl *)

let add_ty_decl tk dl = add_decl tk (create_ty_decl dl)
let add_logic_decl tk dl = add_decl tk (create_logic_decl dl)
let add_ind_decl tk dl = add_decl tk (create_ind_decl dl)
let add_prop_decl tk k p f = add_decl tk (create_prop_decl k p f)

let add_ty_decls tk dl = List.fold_left add_decl tk (create_ty_decls dl)
let add_logic_decls tk dl = List.fold_left add_decl tk (create_logic_decls dl)
let add_ind_decls tk dl = List.fold_left add_decl tk (create_ind_decls dl)

(* use, clone and split_theory *)

let rec use_export task th = match task with
  | Some task_hd when Mid.mem th.th_name task_hd.task_used -> task
  | _ -> add_tdecl (List.fold_left flat_tdecl task th.th_decls) (Use th)

and flat_tdecl task td = match td with
  | Decl { d_node = Dprop (Pgoal,_,_) } -> task
  | Decl { d_node = Dprop (Plemma,pr,f) } -> add_prop_decl task Paxiom pr f
  | Decl _  -> add_tdecl task td
  | Clone _ -> add_tdecl task td
  | Use th -> use_export task th

let clone_export = clone_theory flat_tdecl

let split_tdecl names (res,task) td = match td with
  | Decl { d_node = Dprop (Pgoal,pr,_) }
    when option_apply true (Spr.mem pr) names ->
      add_tdecl task td :: res, task
  | Decl { d_node = Dprop (Pgoal,_,_) } ->
      res, task
  | Decl { d_node = Dprop (Plemma,pr,f) }
    when option_apply true (Spr.mem pr) names ->
      add_prop_decl task Pgoal pr f :: res,
      add_prop_decl task Paxiom pr f
  | Decl { d_node = Dprop (Plemma,pr,f) } ->
      res, add_prop_decl task Paxiom pr f
  | Decl _  -> res, add_tdecl task td
  | Clone _ -> res, add_tdecl task td
  | Use th -> res, use_export task th

let split_theory th names =
  fst (List.fold_left (split_tdecl names) ([],None) th.th_decls)

(* Generic utilities *)

let rec task_fold fn acc = function
  | Some task -> task_fold fn (fn acc task.task_decl) task.task_prev
  | None      -> acc

let rec task_iter fn = function
  | Some task -> fn task.task_decl; task_iter fn task.task_prev
  | None      -> ()

let task_tdecls = task_fold (fun acc d -> d::acc) []

let task_decls =
  task_fold (fun acc -> function Decl d -> d::acc | _ -> acc) []

exception GoalNotFound

let task_goal = function
  | Some { task_decl = Decl { d_node = Dprop (Pgoal,pr,_) }} -> pr
  | _ -> raise GoalNotFound

