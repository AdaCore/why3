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
  tds_tag : Hashweak.tag;
}

module Hstds = Hashcons.Make (struct
  type t = tdecl_set
  let equal s1 s2 = Stdecl.equal s1.tds_set s2.tds_set
  let hs_td td acc = Hashcons.combine acc (td_hash td)
  let hash s = Stdecl.fold hs_td s.tds_set 0
  let tag n s = { s with tds_tag = Hashweak.create_tag n }
end)

let mk_tds s = Hstds.hashcons {
  tds_set = s;
  tds_tag = Hashweak.dummy_tag;
}

let empty_tds = mk_tds Stdecl.empty
let tds_add td s = mk_tds (Stdecl.add td s.tds_set)
let tds_singleton td = mk_tds (Stdecl.singleton td)

let tds_equal = (==)
let tds_hash tds = Hashweak.tag_hash tds.tds_tag

type clone_map = tdecl_set Mid.t
type meta_map = tdecl_set Mmeta.t

let cm_find cm th = try Mid.find th.th_name cm with Not_found -> empty_tds

let mm_find mm t =
  try Mmeta.find t mm with Not_found -> empty_tds

let cm_add cm th td = Mid.add th.th_name (tds_add td (cm_find cm th)) cm

let mm_add mm t td = if t.meta_excl
  then Mmeta.add t (tds_singleton td) mm
  else Mmeta.add t (tds_add td (mm_find mm t)) mm

(** Task *)

type task = task_hd option

and task_hd = {
  task_decl  : tdecl;        (* last declaration *)
  task_prev  : task;         (* context *)
  task_known : known_map;    (* known identifiers *)
  task_clone : clone_map;    (* cloning history *)
  task_meta  : meta_map;     (* meta properties *)
  task_tag   : Hashweak.tag; (* unique magical tag *)
}

let task_hd_equal = (==)

let task_hd_hash t = Hashweak.tag_hash t.task_tag

let task_equal t1 t2 = match t1, t2 with
  | Some t1, Some t2 -> task_hd_equal t1 t2
  | None, None -> true
  | _ -> false

let task_hash t = option_apply 0 (fun t -> task_hd_hash t + 1) t

module Hstask = Hashcons.Make (struct
  type t = task_hd

  let equal t1 t2 = td_equal t1.task_decl t2.task_decl &&
                  task_equal t1.task_prev t2.task_prev

  let hash t = Hashcons.combine (td_hash t.task_decl) (task_hash t.task_prev)

  let tag i task = { task with task_tag = Hashweak.create_tag i }
end)

let mk_task decl prev known clone meta = Some (Hstask.hashcons {
  task_decl  = decl;
  task_prev  = prev;
  task_known = known;
  task_clone = clone;
  task_meta  = meta;
  task_tag   = Hashweak.dummy_tag;
})

let task_known = option_apply Mid.empty (fun t -> t.task_known)
let task_clone = option_apply Mid.empty (fun t -> t.task_clone)
let task_meta  = option_apply Mmeta.empty (fun t -> t.task_meta)

let find_clone task th = cm_find (task_clone task) th
let find_meta  task t  = mm_find (task_meta  task) t

(* constructors with checks *)

exception LemmaFound
exception SkipFound
exception GoalFound
exception GoalNotFound

let find_goal = function
  | Some {task_decl = {td_node = Decl {d_node = Dprop (Pgoal,p,_)}}} -> Some p
  | _ -> None

let task_goal task  = match find_goal task with
  | Some pr -> pr
  | None    -> raise GoalNotFound

let check_task task = match find_goal task with
  | Some _  -> raise GoalFound
  | None    -> task

let check_decl = function
  | { d_node = Dprop (Plemma,_,_)} -> raise LemmaFound
  | { d_node = Dprop (Pskip,_,_)}  -> raise SkipFound
  | d -> d

let new_decl task d td =
  let kn = known_add_decl (task_known task) (check_decl d) in
  mk_task td (check_task task) kn (task_clone task) (task_meta task)

let new_decl task d td = try new_decl task d td with KnownIdent _ -> task

let new_clone task th td =
  let cl = cm_add (task_clone task) th td in
  mk_task td (check_task task) (task_known task) cl (task_meta task)

let new_meta task t td =
  let mt = mm_add (task_meta task) t td in
  mk_task td (check_task task) (task_known task) (task_clone task) mt

(* declaration constructors + add_decl *)

let add_decl task d = new_decl task d (create_decl d)

let add_ty_decl tk dl = add_decl tk (create_ty_decl dl)
let add_logic_decl tk dl = add_decl tk (create_logic_decl dl)
let add_ind_decl tk dl = add_decl tk (create_ind_decl dl)
let add_prop_decl tk k p f = add_decl tk (create_prop_decl k p f)

(* task constructors *)

let rec add_tdecl task td = match td.td_node with
  | Decl d -> new_decl task d td
  | Use th -> use_export task th
  | Clone (th,_,_,_) -> new_clone task th td
  | Meta (t,_) -> new_meta task t td

and flat_tdecl task td = match td.td_node with
  | Decl { d_node = Dprop (Plemma,pr,f) } -> add_prop_decl task Paxiom pr f
  | Decl { d_node = Dprop ((Pgoal|Pskip),_,_) } -> task
  | _ -> add_tdecl task td

and use_export task th =
  let td = create_null_clone th in
  if Stdecl.mem td (find_clone task th).tds_set then task else
  let task = List.fold_left flat_tdecl task th.th_decls in
  new_clone task th td

let clone_export = clone_theory flat_tdecl

let add_meta task t al = new_meta task t (create_meta t al)

(* split theory *)

let split_tdecl names (res,task) td = match td.td_node with
  | Decl { d_node = Dprop ((Pgoal|Plemma),pr,f) }
    when option_apply true (Spr.mem pr) names ->
      let res = add_prop_decl task Pgoal pr f :: res in
      res, flat_tdecl task td
  | _ ->
      res, flat_tdecl task td

let split_theory th names init =
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

exception NotTaggingMeta of meta

let find_tagged_ts t tds acc =
  begin match t.meta_type with
    | [MTtysymbol] -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  Stdecl.fold (fun td acc -> match td.td_node with
    | Meta (s, [MAts ts]) when meta_equal s t -> Sts.add ts acc
    | _ -> assert false) tds.tds_set acc

let find_tagged_ls t tds acc =
  begin match t.meta_type with
    | [MTlsymbol] -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  Stdecl.fold (fun td acc -> match td.td_node with
    | Meta (s, [MAls ls]) when meta_equal s t -> Sls.add ls acc
    | _ -> assert false) tds.tds_set acc

let find_tagged_pr t tds acc =
  begin match t.meta_type with
    | [MTprsymbol] -> ()
    | _ -> raise (NotTaggingMeta t)
  end;
  Stdecl.fold (fun td acc -> match td.td_node with
    | Meta (s, [MApr pr]) when meta_equal s t -> Spr.add pr acc
    | _ -> assert false) tds.tds_set acc

exception NotExclusiveMeta of meta

let get_meta_excl t tds =
  if not t.meta_excl then raise (NotExclusiveMeta t);
  Stdecl.fold (fun td _ -> match td.td_node with
    | Meta (s,arg) when s = t -> Some arg
    | _ -> assert false) tds.tds_set None

(* Exception reporting *)

let () = Exn_printer.register (fun fmt exn -> match exn with
  | LemmaFound ->   Format.fprintf fmt "Task cannot contain a lemma"
  | SkipFound ->    Format.fprintf fmt "Task cannot contain a skip"
  | GoalFound ->    Format.fprintf fmt "The task already ends with a goal"
  | GoalNotFound -> Format.fprintf fmt "The task does not end with a goal"
  | NotTaggingMeta m ->
      Format.fprintf fmt "Metaproperty '%s' is not a symbol tag" m.meta_name
  | NotExclusiveMeta m ->
      Format.fprintf fmt "Metaproperty '%s' is not exclusive" m.meta_name
  | _ -> raise exn)

