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

(** Environment *)

type env

type retrieve_theory = env -> string list -> theory Mnm.t

val create_env : retrieve_theory -> env

val find_theory : env -> string list -> string -> theory

val env_tag : env -> int

exception TheoryNotFound of string list * string

(** Cloning map *)

type clone = private {
  cl_map : Sid.t Mid.t;
  cl_tag : int
}

val cloned_from : clone -> ident -> ident -> bool

(** Task *)

type task = private {
  task_decl  : decl;
  task_prev  : task option;
  task_known : decl Mid.t;
  task_clone : clone;
  task_env   : env;
  task_tag   : int;
}

val add_decl : task -> decl -> task

(* bottom-up, tail-recursive traversal functions *)

val task_fold : ('a -> decl -> 'a) -> 'a -> task -> 'a
val task_iter : (decl -> unit) -> task -> unit

(* top-down list of declarations *)
val task_decls : task -> decl list

(* exceptions *)

exception UnknownIdent of ident
exception RedeclaredIdent of ident

