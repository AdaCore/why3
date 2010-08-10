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

(** Clone and meta history *)

type tdecl_set = {
  tds_set : Stdecl.t;
  tds_tag : int;
}

module Hstds = Hashcons.Make (struct
  type t = tdecl_set
  let equal s1 s2 = Stdecl.equal s1.tds_set s2.tds_set
  let hs_td td acc = Hashcons.combine acc td.td_tag
  let hash s = Stdecl.fold hs_td s.tds_set 0
  let tag n s = { s with tds_tag = n }
end)

let mk_tds s = Hstds.hashcons { tds_set = s; tds_tag = -1 }

let empty_tds = mk_tds Stdecl.empty
let tds_add td s = mk_tds (Stdecl.add td s.tds_set)
let tds_singleton td = mk_tds (Stdecl.singleton td)

let tds_equal = (==)

type clone_map = tdecl_set Mid.t
type meta_map = tdecl_set Mstr.t

let cm_find cm th = try Mid.find th.th_name cm with Not_found -> empty_tds

let mm_find mm t =
  try Mstr.find t mm with Not_found -> ignore (lookup_meta t); empty_tds

let cm_add cm th td = Mid.add th.th_name (tds_add td (cm_find cm th)) cm

let mm_add mm t td = if is_meta_excl t
  then Mstr.add t (tds_singleton td) mm
  else Mstr.add t (tds_add td (mm_find mm t)) mm

(** Task *)

type task = task_hd option

and task_hd = {
  task_decl  : tdecl;       (* last declaration *)
  task_prev  : task;        (* context *)
  task_known : known_map;   (* known identifiers *)
  task_clone : clone_map;   (* cloning history *)
  task_meta  : meta_map;    (* meta properties *)
  task_tag   : int;         (* unique task tag *)
}

let task_hd_equal = (==)

let task_equal t1 t2 = match t1, t2 with
  | Some t1, Some t2 -> task_hd_equal t1 t2
  | None, None -> true
  | _ -> false

module Hstask = Hashcons.Make (struct
  type t = task_hd

  let equal t1 t2 = td_equal t1.task_decl t2.task_decl &&
                  task_equal t1.task_prev t2.task_prev

  let hash task =
    let decl = task.task_decl.td_tag in
    let prev = option_apply 0 (fun t -> t.task_tag + 1) task.task_prev in
    Hashcons.combine decl prev

  let tag i task = { task with task_tag = i }
end)

let mk_task decl prev known clone meta = Some (Hstask.hashcons {
  task_decl  = decl;
  task_prev  = prev;
  task_known = known;
  task_clone = clone;
  task_meta  = meta;
  task_tag   = -1;
})

let task_known = option_apply Mid.empty (fun t -> t.task_known)
let task_clone = option_apply Mid.empty (fun t -> t.task_clone)
let task_meta  = option_apply Mstr.empty (fun t -> t.task_meta)

let find_clone task th = cm_find (task_clone task) th
let find_meta  task t  = mm_find (task_meta  task) t

let add_decl task d td =
  let kn = known_add_decl (task_known task) d in
  mk_task td task kn (task_clone task) (task_meta task)

let add_clone task th td =
  let cl = cm_add (task_clone task) th td in
  mk_task td task (task_known task) cl (task_meta task)

let add_meta task t td =
  let mt = mm_add (task_meta task) t td in
  mk_task td task (task_known task) (task_clone task) mt

(* add_decl with checks *)

exception LemmaFound
exception SkipFound
exception GoalFound
exception GoalNotFound

let rec task_goal = function
  | Some task ->
      begin match task.task_decl.td_node with
        | Decl { d_node = Dprop (Pgoal,pr,_) } -> pr
        | Decl _ -> raise GoalNotFound
        | _ -> task_goal task.task_prev
      end
  | None -> raise GoalNotFound

let new_decl task d td = match d.d_node with
  | Dprop (Plemma,_,_) -> raise LemmaFound
  | Dprop (Pskip,_,_)  -> raise SkipFound
  | _ ->
      try ignore (task_goal task); raise GoalFound
      with GoalNotFound -> try add_decl task d td
      with KnownIdent _ -> task

(* declaration constructors + add_decl *)

let add_decl task d = new_decl task d (create_decl d)

let add_ty_decl tk dl = add_decl tk (create_ty_decl dl)
let add_logic_decl tk dl = add_decl tk (create_logic_decl dl)
let add_ind_decl tk dl = add_decl tk (create_ind_decl dl)
let add_prop_decl tk k p f = add_decl tk (create_prop_decl k p f)

let add_ty_decls tk dl = List.fold_left add_decl tk (create_ty_decls dl)
let add_logic_decls tk dl = List.fold_left add_decl tk (create_logic_decls dl)
let add_ind_decls tk dl = List.fold_left add_decl tk (create_ind_decls dl)

(* task constructors *)

let rec add_tdecl task td = match td.td_node with
  | Decl d -> new_decl task d td
  | Use th -> use_export task th
  | Clone (th,_,_,_) -> add_clone task th td
  | Meta (t,_) -> add_meta task t td

and flat_tdecl task td = match td.td_node with
  | Decl { d_node = Dprop (Plemma,pr,f) } -> add_prop_decl task Paxiom pr f
  | Decl { d_node = Dprop ((Pgoal|Pskip),_,_) } -> task
  | _ -> add_tdecl task td

and use_export task th =
  let td = create_null_clone th in
  if Stdecl.mem td (find_clone task th).tds_set then task else
  let task = List.fold_left flat_tdecl task th.th_decls in
  add_clone task th td

let clone_export = clone_theory flat_tdecl

let add_meta task t al = add_meta task t (create_meta t al)

(* split theory *)

let split_tdecl names (res,task) td = match td.td_node with
  | Decl { d_node = Dprop ((Pgoal|Plemma),pr,f) }
    when option_apply true (Spr.mem pr) names ->
      let res = add_prop_decl task Pgoal pr f :: res in
      res, flat_tdecl task td
  | _ ->
      res, flat_tdecl task td

let split_theory ?(init=None) th names =
  fst (List.fold_left (split_tdecl names) ([],init) th.th_decls)

(* Generic utilities *)

let rec task_fold fn acc = function
  | Some task -> task_fold fn (fn acc task.task_decl) task.task_prev
  | None      -> acc

let rec task_iter fn = function
  | Some task -> fn task.task_decl; task_iter fn task.task_prev
  | None      -> ()

let task_tdecls = task_fold (fun acc td -> td::acc) []

let task_decls  = task_fold (fun acc td ->
  match td.td_node with Decl d -> d::acc | _ -> acc) []

(* special selector for metaproperties of a single ident *)

exception NotTaggingMeta of string

let find_tagged_ts t tds acc =
  begin match lookup_meta t with
    | [MTtysymbol] -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  Stdecl.fold (fun td acc -> match td.td_node with
    | Meta (s, [MAts ts]) when s = t -> Sts.add ts acc
    | _ -> assert false) tds.tds_set acc

let find_tagged_ls t tds acc =
  begin match lookup_meta t with
    | [MTlsymbol] -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  Stdecl.fold (fun td acc -> match td.td_node with
    | Meta (s, [MAls ls]) when s = t -> Sls.add ls acc
    | _ -> assert false) tds.tds_set acc

let find_tagged_pr t tds acc =
  begin match lookup_meta t with
    | [MTprsymbol] -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  Stdecl.fold (fun td acc -> match td.td_node with
    | Meta (s, [MApr pr]) when s = t -> Spr.add pr acc
    | _ -> assert false) tds.tds_set acc

exception NotExclusiveMeta of string

let get_meta_exc t tds =
  if not (is_meta_excl t) then raise (NotExclusiveMeta t);
  Stdecl.fold (fun td _ -> match td.td_node with
    | Meta (s,_) when s = t -> Some td
    | _ -> assert false) tds.tds_set None

(* Exception reporting *)

let () = Exn_printer.register (fun fmt exn -> match exn with
  | LemmaFound ->   Format.fprintf fmt "Task cannot contain a lemma"
  | SkipFound ->    Format.fprintf fmt "Task cannot contain a skip"
  | GoalFound ->    Format.fprintf fmt "The task already ends with a goal"
  | GoalNotFound -> Format.fprintf fmt "The task does not end with a goal"
  | NotTaggingMeta s ->
      Format.fprintf fmt "Metaproperty '%s' is not a symbol tag" s
  | NotExclusiveMeta s ->
      Format.fprintf fmt "Metaproperty '%s' is not exclusive" s
  | _ -> raise exn)

