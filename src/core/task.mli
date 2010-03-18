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

(** Cloning map *)

type clone = private {
  cl_map : clone_map;
  cl_tag : int
}

val cloned_from : clone -> ident -> ident -> bool

(** Task *)

type task = task_hd option

and task_hd = private {
  task_decl  : decl;
  task_prev  : task;
  task_known : decl Mid.t;
  task_tag   : int;
}

(* constructors *)

val add_decl : task -> decl -> task

val split_theory : theory -> Spr.t option -> (task * clone) list

(* bottom-up, tail-recursive traversal functions *)

val task_fold : ('a -> decl -> 'a) -> 'a -> task -> 'a

val task_iter : (decl -> unit) -> task -> unit

val task_decls : task -> decl list

val task_goal : task -> prsymbol

(* exceptions *)

exception UnknownIdent of ident
exception RedeclaredIdent of ident
exception GoalNotFound
exception GoalFound
exception LemmaFound

