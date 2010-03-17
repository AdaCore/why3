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
open Theory2

(** Cloning map *)

type clone

val cloned_from : clone -> ident -> ident -> bool

val clone_tag : clone -> int

(** Task *)

type task = task_hd option

and task_hd = private {
  task_decl  : decl;
  task_prev  : task;
  task_known : decl Mid.t;
  task_tag   : int;
}

(* constructors *)

(* val init_task : task *)
(* val add_decl : task -> decl -> task *)

val add_decl : task -> decl -> task

val split_theory : theory -> Spr.t -> (task * clone) list

val split_theory_full : theory -> (task * clone) list

(* bottom-up, tail-recursive traversal functions *)

val task_fold : ('a -> decl -> 'a) -> 'a -> task -> 'a

val task_iter : (decl -> unit) -> task -> unit

val task_decls : task -> decl list

val task_goal : task -> prop

(* exceptions *)

exception UnknownIdent of ident
exception RedeclaredIdent of ident
exception GoalNotFound

(** Task transformation *)

module Tr : sig

type 'a trans
type 'a tlist = 'a list trans

val identity   : task trans
val identity_l : task tlist

val apply : 'a trans -> (task -> 'a)
val store : (task -> 'a) -> 'a trans

val singleton : 'a trans -> 'a tlist

val compose   : task trans -> 'a trans -> 'a trans
val compose_l : task tlist -> 'a tlist -> 'a tlist

(* val conv_res : 'a trans -> ('a -> 'b) -> 'b trans *)

val fold   : (task_hd -> 'a -> 'a     ) -> 'a -> 'a trans
val fold_l : (task_hd -> 'a -> 'a list) -> 'a -> 'a tlist

val fold_map :
  (task_hd -> 'a * task -> ('a * task)     ) -> 'a -> task trans

val fold_map_l :
  (task_hd -> 'a * task -> ('a * task) list) -> 'a -> task tlist

val map   : (task_hd -> task -> task     ) -> task trans
val map_l : (task_hd -> task -> task list) -> task tlist

val decl   : (decl -> decl list     ) -> task trans
val decl_l : (decl -> decl list list) -> task tlist

val expr : (term -> term) -> (fmla -> fmla) -> task trans

end

