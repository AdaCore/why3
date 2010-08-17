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

type tdecl_set = private {
  tds_set : Stdecl.t;
  tds_tag : int;
}

val tds_equal : tdecl_set -> tdecl_set -> bool

type clone_map = tdecl_set Mid.t
type meta_map = tdecl_set Mmeta.t

(** Task *)

type task = task_hd option

and task_hd = private {
  task_decl  : tdecl;       (* last declaration *)
  task_prev  : task;        (* context *)
  task_known : known_map;   (* known identifiers *)
  task_clone : clone_map;   (* cloning history *)
  task_meta  : meta_map;    (* meta properties *)
  task_tag   : int;         (* unique task tag *)
}

val task_equal : task -> task -> bool
val task_hd_equal : task_hd -> task_hd -> bool

val task_known : task -> known_map
val task_clone : task -> clone_map
val task_meta  : task -> meta_map

val find_clone : task -> theory -> tdecl_set
val find_meta  : task -> meta -> tdecl_set

(** {2 constructors} *)

val add_decl : task -> decl -> task
val add_tdecl : task -> tdecl -> task

val use_export : task -> theory -> task
val clone_export : task -> theory -> th_inst -> task
val add_meta : task -> meta -> meta_arg list -> task

(** {2 declaration constructors + add_decl} *)

val add_ty_decl : task -> ty_decl list -> task
val add_logic_decl : task -> logic_decl list -> task
val add_ind_decl : task -> ind_decl list -> task
val add_prop_decl : task -> prop_kind -> prsymbol -> fmla -> task

val add_ty_decls : task -> ty_decl list -> task
val add_logic_decls : task -> logic_decl list -> task
val add_ind_decls : task -> ind_decl list -> task

(** {2 utilities} *)

val split_theory : theory -> Spr.t option -> task -> task list
  (** [split_theory th s] returns the tasks of [th] which end by one
      of [s]. They are in the opposite order than in the theory *)

(** {2 bottom-up, tail-recursive traversal functions} *)

val task_fold : ('a -> tdecl -> 'a) -> 'a -> task -> 'a
val task_iter : (tdecl -> unit) -> task -> unit

val task_tdecls : task -> tdecl list
val task_decls  : task -> decl list

val task_goal  : task -> prsymbol

(* special selector for metaproperties of a single ident *)

exception NotTaggingMeta of meta

val find_tagged_ts : meta -> tdecl_set -> Sts.t -> Sts.t
val find_tagged_ls : meta -> tdecl_set -> Sls.t -> Sls.t
val find_tagged_pr : meta -> tdecl_set -> Spr.t -> Spr.t

(* special selector for exclusive metaproperties *)

exception NotExclusiveMeta of meta

val get_meta_excl : meta -> tdecl_set -> meta_arg list option

(* exceptions *)

exception GoalNotFound
exception GoalFound
exception SkipFound
exception LemmaFound

