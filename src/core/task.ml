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

(** Cloning map *)

type clone = {
  cl_map : clone_map;
  cl_tag : int
}

let empty_clone = {
  cl_map = Mid.empty;
  cl_tag = 0;
}

let cloned_from cl i1 i2 =
  try i1 = i2 || Sid.mem i2 (Mid.find i1 cl.cl_map)
  with Not_found -> false

let add_clone =
  let r = ref 0 in
  fun cl th sl ->
    incr r;
    { cl_map = merge_clone cl.cl_map th sl; cl_tag = !r }


(** Task *)

type task = task_hd option

and task_hd = {
  task_decl  : decl;
  task_prev  : task;
  task_known : known;
  task_tag   : int;
}

module Task = struct
  type t = task_hd

  let equal a b =
    a.task_decl == b.task_decl &&
    match a.task_prev, b.task_prev with
      | Some na, Some nb -> na == nb
      | None, None -> true
      | _ -> false

  let hash task =
    let prev = match task.task_prev with
      | Some task -> 1 + task.task_tag
      | None -> 0
    in
    Hashcons.combine task.task_decl.d_tag prev

  let tag i task = { task with task_tag = i }
end
module Htask = Hashcons.Make(Task)

let mk_task decl prev known = Htask.hashcons {
  task_decl  = decl;
  task_prev  = prev;
  task_known = known;
  task_tag   = -1;
}

exception LemmaFound
exception GoalFound

let push_decl task d =
  begin match task.task_decl.d_node with
    | Dprop (Pgoal,_,_) -> raise GoalFound
    | _ -> ()
  end;
  try mk_task d (Some task) (kn_add_decl task.task_known d)
  with KnownIdent _ -> task

let init_decl d =
  try mk_task d None (kn_add_decl Mid.empty d)
  with KnownIdent _ -> assert false

let add_decl opt d =
  begin match d.d_node with
    | Dprop (Plemma,_,_) -> raise LemmaFound
    | _ -> ()
  end;
  match opt with
    | Some task -> Some (push_decl task d)
    | None      -> Some (init_decl d)

let rec flat_theory used cl task th =
  if Sid.mem th.th_name used then used,cl,task else
  let acc = Sid.add th.th_name used, cl, task in
  List.fold_left flat_tdecl acc th.th_decls

and flat_tdecl (used, cl, task) = function
  | Use th ->
      flat_theory used cl task th
  | Clone (th,sl) ->
      used, add_clone cl th sl, task
  | Decl d ->
      begin match d.d_node with
        | Dprop (Pgoal,_,_) ->
            used, cl, task
        | Dprop (Plemma,pr,f) ->
            let d = create_prop_decl Paxiom pr f in
            used, cl, add_decl task d
        | Dprop (Paxiom,_,_) ->
            used, cl, add_decl task d
        | Dtype _ | Dlogic _ | Dind _  ->
            used, cl, add_decl task d
      end

let split_tdecl names (res, used, cl, task) = function
  | Use th ->
      let used, cl, task = flat_theory used cl task th in
      res, used, cl, task
  | Clone (th,sl) ->
      res, used, add_clone cl th sl, task
  | Decl d ->
      begin match d.d_node with
        | Dprop (Pgoal,pr,_)
          when option_apply true (Spr.mem pr) names ->
            let t = add_decl task d, cl in
            t :: res, used, cl, task
        | Dprop (Pgoal,_,_) ->
            res, used, cl, task
        | Dprop (Plemma,pr,f)
          when option_apply true (Spr.mem pr) names ->
            let d = create_prop_decl Pgoal pr f in
            let t = add_decl task d, cl in
            let d = create_prop_decl Paxiom pr f in
            t :: res, used, cl, add_decl task d
        | Dprop (Plemma,pr,f) ->
            let d = create_prop_decl Paxiom pr f in
            res, used, cl, add_decl task d
        | Dprop (Paxiom,_,_) ->
            res, used, cl, add_decl task d
        | Dtype _ | Dlogic _ | Dind _  ->
            res, used, cl, add_decl task d
      end

let split_theory th names =
  let acc = [], Sid.empty, empty_clone, None in
  let res,_,_,_ = List.fold_left (split_tdecl names) acc th.th_decls in
  res

let flat_theory task th =
  let _,_,task = flat_theory Sid.empty empty_clone task th in
  task

(* Generic utilities *)

let rec task_fold fn acc = function
  | Some task -> task_fold fn (fn acc task.task_decl) task.task_prev
  | None      -> acc

let rec task_iter fn = function
  | Some task -> fn task.task_decl; task_iter fn task.task_prev
  | None      -> ()

let task_decls = task_fold (fun acc d -> d::acc) []

exception GoalNotFound

let task_goal = function
  | Some { task_decl = { d_node = Dprop (Pgoal,pr,_) }} -> pr
  | _ -> raise GoalNotFound

