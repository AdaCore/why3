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

open Format
open Util
open Ident
open Ty
open Term
open Termlib
open Decl
open Theory2

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

let clone_tag cl = cl.cl_tag


(** Known identifiers *)

exception UnknownIdent of ident
exception RedeclaredIdent of ident

let known_id kn id =
  if not (Mid.mem id kn) then raise (UnknownIdent id)

let known_ts kn () ts = known_id kn ts.ts_name
let known_ls kn () ls = known_id kn ls.ls_name

let known_ty kn ty = ty_s_fold (known_ts kn) () ty
let known_term kn t = t_s_fold (known_ts kn) (known_ls kn) () t
let known_fmla kn f = f_s_fold (known_ts kn) (known_ls kn) () f

let merge_known kn1 kn2 =
  let add_known id decl kn =
    try
      if Mid.find id kn2 != decl then raise (RedeclaredIdent id);
      kn
    with Not_found -> Mid.add id decl kn
  in
  Mid.fold add_known kn1 kn2

exception DejaVu

let add_known id decl kn =
  try
    if Mid.find id kn != decl then raise (RedeclaredIdent id);
    raise DejaVu
  with Not_found -> Mid.add id decl kn

let add_constr d kn fs = add_known fs.ls_name d kn

let add_type d kn (ts,def) =
  let kn = add_known ts.ts_name d kn in
  match def with
    | Tabstract -> kn
    | Talgebraic lfs -> List.fold_left (add_constr d) kn lfs

let check_type kn (ts,def) =
  let check_constr fs = List.iter (known_ty kn) fs.ls_args in
  match def with
    | Tabstract -> option_iter (known_ty kn) ts.ts_def
    | Talgebraic lfs -> List.iter check_constr lfs

let add_logic d kn (ls,_) = add_known ls.ls_name d kn

let check_ls_defn kn ld =
  let _,e = open_ls_defn ld in
  e_apply (known_term kn) (known_fmla kn) e

let check_logic kn (ls,ld) =
  List.iter (known_ty kn) ls.ls_args;
  option_iter (known_ty kn) ls.ls_value;
  option_iter (check_ls_defn kn) ld

let add_ind d kn (ps,la) =
    let kn = add_known ps.ls_name d kn in
    let add kn (pr,_) = add_known (pr_name pr) d kn in
    List.fold_left add kn la

let check_ind kn (ps,la) =
    List.iter (known_ty kn) ps.ls_args;
    let check (_,f) = known_fmla kn f in
    List.iter check la

let add_decl kn d = match d.d_node with
  | Dtype dl  -> List.fold_left (add_type d) kn dl
  | Dlogic dl -> List.fold_left (add_logic d) kn dl
  | Dind dl   -> List.fold_left (add_ind d) kn dl
  | Dprop (_,pr,_) -> add_known (pr_name pr) d kn

let check_decl kn d = match d.d_node with
  | Dtype dl  -> List.iter (check_type kn) dl
  | Dlogic dl -> List.iter (check_logic kn) dl
  | Dind dl   -> List.iter (check_ind kn) dl
  | Dprop (_,_,f) -> known_fmla kn f


(** Task *)

type task = {
  task_decl  : decl;
  task_prev  : task option;
  task_known : decl Mid.t;
  task_tag   : int;
}

module Task = struct
  type t = task

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

let push_decl task d =
  try 
    let kn = add_decl task.task_known d in
    ignore (check_decl kn d);
    mk_task d (Some task) kn
  with DejaVu -> task

let init_decl d =  
  try
    let kn = add_decl Mid.empty d in
    ignore (check_decl kn d);
    mk_task d None kn
  with DejaVu -> assert false

let add_decl opt d =
  match opt with
    | Some task -> push_decl task d
    | None -> init_decl d

let init_task =
  let add opt = function
    | Decl d -> Some (add_decl opt d)
    | _      -> opt
  in
  List.fold_left add None builtin_theory.th_decls

(* let init_task = of_option init_task *)

let rec use_export names acc td =
  let used, cl, res, task = acc in
  match td with
    | Use th when Sid.mem th.th_name used ->
        acc
    | Use th ->
        let used = Sid.add th.th_name used in
        let acc = used, cl, res, task in
        let names = Some Spr.empty in
        List.fold_left (use_export names) acc th.th_decls
    | Clone (th,sl) ->
        let cl = add_clone cl th sl in
        used, cl, res, task
    | Decl d ->
        begin match d.d_node with
          | Dprop (Pgoal,pr,_)
            when option_apply true (Spr.mem pr) names ->
              let res = (push_decl task d, cl) :: res in
              used, cl, res, task
          | Dprop (Pgoal,_,_) ->
              acc
          | Dprop (Plemma,pr,f)
            when option_apply true (Spr.mem pr) names ->
              let d = create_prop_decl Pgoal pr f in
              let res = (push_decl task d, cl) :: res in
              let d = create_prop_decl Paxiom pr f in
              used, cl, res, push_decl task d
          | Dprop (Plemma,pr,f) ->
              let d = create_prop_decl Paxiom pr f in
              used, cl, res, push_decl task d
          | Dprop (Paxiom,_,_) ->
              used, cl, res, push_decl task d
          | Dtype _ | Dlogic _ | Dind _  ->
              used, cl, res, push_decl task d
        end

let split_theory_opt th names =
  let acc = Sid.empty, empty_clone, [], of_option init_task in
  let _, _, res, _ =
    List.fold_left (use_export names) acc th.th_decls
  in
  res

let split_theory th names = split_theory_opt th (Some names)
let split_theory_full th  = split_theory_opt th  None

(* Generic utilities *)

let rec task_fold fn acc task =
  let acc = fn acc task.task_decl in
  match task.task_prev with
    | Some task -> task_fold fn acc task
    | None -> acc

let rec task_iter fn task =
  fn task.task_decl;
  match task.task_prev with
    | Some task -> task_iter fn task
    | None -> ()

let task_decls = task_fold (fun acc d -> d::acc) []

exception GoalNotFound

let task_goal task = match task.task_decl.d_node with
  | Dprop (Pgoal,pr,_) -> pr
  | _ -> raise GoalNotFound


(** Task transformation *)

module Tr = struct

type 'a trans = task -> 'a
type 'a tlist = 'a list trans

let identity   x = x
let identity_l x = [x]

let conv_res f c x = c (f x)

let singleton f x = [f x]

let compose f g x = g (f x)

let compose_l f g x =
  List.fold_left (fun acc l -> List.rev_append (g l) acc) [] (f x)

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
let task_tag t = t.task_tag

let store f = memo f task_tag (Hashtbl.create 63)

let fold   fn v = assert false (* TODO *)
let fold_l fn v = assert false (* TODO *)

let fold_map   fn v = conv_res (fold   fn (v, init_task)) snd
let fold_map_l fn v = conv_res (fold_l fn (v, init_task)) (List.rev_map snd)

let map   fn = fold   (fun t1 t2 -> fn t1 t2) init_task
let map_l fn = fold_l (fun t1 t2 -> fn t1 t2) init_task

let decl   fn = assert false (* TODO *)
let decl_l fn = assert false (* TODO *)

let expr fnT fnF d = assert false (* TODO *)

end
