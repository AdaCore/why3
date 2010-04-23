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
open Ty
open Term
open Decl
open Theory

(** Task *)

type task = task_hd option

and task_hd = private {
  task_decl  : tdecl;       (* last declaration *)
  task_prev  : task;        (* context *)
  task_known : known_map;   (* known identifiers *)
  task_clone : clone_map;   (* cloning history *)
  task_used  : use_map;     (* referenced theories *)
  task_tag   : int;         (* unique task tag *)
}

and tdecl = private
  | Decl  of decl
  | Use   of theory
  | Clone of theory * (ident * ident) list

val task_known : task -> known_map
val task_clone : task -> clone_map
val task_used  : task -> use_map

(* constructors *)

val add_tdecl : task -> tdecl -> task
val add_decl : task -> decl -> task

val use_export : task -> theory -> task
val clone_export : task -> theory -> th_inst -> task

(* declaration constructors + add_decl *)

val add_ty_decl : task -> ty_decl list -> task
val add_logic_decl : task -> logic_decl list -> task
val add_ind_decl : task -> ind_decl list -> task
val add_prop_decl : task -> prop_kind -> prsymbol -> fmla -> task

val add_ty_decls : task -> ty_decl list -> task
val add_logic_decls : task -> logic_decl list -> task
val add_ind_decls : task -> ind_decl list -> task

(* utilities *)

val split_theory : theory -> Spr.t option -> task list

(* bottom-up, tail-recursive traversal functions *)

val task_fold : ('a -> tdecl -> 'a) -> 'a -> task -> 'a
val task_iter : (tdecl -> unit) -> task -> unit
val task_tdecls : task -> tdecl list
val task_decls : task -> decl list

val task_goal  : task -> prsymbol

val last_clone : task -> task
val last_use   : task -> task

(* exceptions *)

exception GoalNotFound
exception GoalFound
exception LemmaFound

