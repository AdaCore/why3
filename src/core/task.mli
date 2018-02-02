(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Proof Tasks, Cloning and Meta History *)

open Ident
open Ty
open Term
open Decl
open Theory

type tdecl_set = private {
  tds_set : Stdecl.t;
  tds_tag : Weakhtbl.tag;
}

val tds_equal : tdecl_set -> tdecl_set -> bool
val tds_hash : tdecl_set -> int
val tds_compare : tdecl_set -> tdecl_set -> int
val tds_empty : tdecl_set

val mk_tds : Stdecl.t -> tdecl_set

type clone_map = tdecl_set Mid.t    (* Use and Clone *)
type meta_map = tdecl_set Mmeta.t   (* Meta *)

(** Task *)

type task = task_hd option

and task_hd = private {
  task_decl  : tdecl;        (** last declaration *)
  task_prev  : task;         (** context *)
  task_known : known_map;    (** known identifiers *)
  task_clone : clone_map;    (** use/clone history *)
  task_meta  : meta_map;     (** meta properties *)
  task_tag   : Weakhtbl.tag; (** unique magical tag *)
}

val task_equal : task -> task -> bool
val task_hd_equal : task_hd -> task_hd -> bool

val task_hash : task -> int
val task_hd_hash : task_hd -> int

val task_known : task -> known_map
val task_clone : task -> clone_map
val task_meta  : task -> meta_map

val find_clone_tds : task -> theory -> tdecl_set
val find_meta_tds  : task -> meta -> tdecl_set

(** {2 Constructors} *)

val add_decl : task -> decl -> task
val add_tdecl : task -> tdecl -> task

val use_export : task -> theory -> task
val clone_export : task -> theory -> th_inst -> task
val add_meta : task -> meta -> meta_arg list -> task

(** {2 Declaration constructors + add_decl} *)

val add_ty_decl : task -> tysymbol -> task
val add_data_decl : task -> data_decl list -> task
val add_param_decl : task -> lsymbol -> task
val add_logic_decl : task -> logic_decl list -> task
val add_ind_decl : task -> ind_sign -> ind_decl list -> task
val add_prop_decl : task -> prop_kind -> prsymbol -> term -> task

(** {2 Utilities} *)

val split_theory : theory -> Spr.t option -> task -> task list
  (** [split_theory th s t] returns the list of proof tasks that
      correspond to goals in [th], in the order of appearance.
      If set [s] is not empty, then only the goals in [s] are
      proved. The goals which are instances of already proved
      propositions (introduced by cloning) are not proved.
      Task [t] is the task prefix that can be used to add
      some metas to every generated proof task. *)

(** {2 Realization utilities} *)

val used_theories : task -> theory Mid.t
  (** returns a map from theory names to theories themselves *)

val used_symbols : theory Mid.t -> theory Mid.t
  (** takes the result of [used_theories] and returns
      a map from symbol names to their theories of origin *)

val local_decls : task -> theory Mid.t -> decl list
  (** takes the result of [used_symbols] and returns
      the list of declarations that are not imported
      with those theories or derived thereof *)

(** {2 Bottom-up, tail-recursive traversal functions} *)

val task_fold : ('a -> tdecl -> 'a) -> 'a -> task -> 'a
val task_iter : (tdecl -> unit) -> task -> unit

val task_tdecls : task -> tdecl list
val task_decls  : task -> decl list

val task_goal  : task -> prsymbol
val task_goal_fmla  : task -> term

val task_separate_goal : task -> tdecl * task
(** [task_separate_goal t] returns a pair [(g,t')] where [g] is the
    goal of the task [t] and [t'] is the rest.  raises [GoalNotFound]
    if task [t] has no goal *)

(** {2 Selectors} *)

val on_meta : meta -> ('a -> meta_arg list -> 'a) -> 'a -> task -> 'a
val on_cloned_theory : theory -> ('a -> symbol_map -> 'a) -> 'a -> task -> 'a

val on_meta_excl : meta -> task -> meta_arg list option
val on_used_theory : theory -> task -> bool

val on_tagged_ty : meta -> task -> Sty.t
val on_tagged_ts : meta -> task -> Sts.t
val on_tagged_ls : meta -> task -> Sls.t
val on_tagged_pr : meta -> task -> Spr.t

(** Exceptions *)

exception NotTaggingMeta of meta
exception NotExclusiveMeta of meta

exception GoalNotFound
exception GoalFound
exception LemmaFound
