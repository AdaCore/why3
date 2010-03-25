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

(** Typing environments *)

open Ty
open Term
open Theory
open Env

val retrieve : string list -> retrieve_theory
  (** creates a new typing environment for a given loadpath *)

val read_file : env -> string -> theory Mnm.t

val read_channel : env -> string -> in_channel -> theory Mnm.t

(** incremental parsing *)

val add_decl : env -> theory Mnm.t -> theory_uc -> Ptree.decl -> theory_uc

type denv

val create_denv : theory_uc -> denv

val find_user_type_var : string -> denv -> Denv.type_var

val mem_var : string -> denv -> bool
val find_var : string -> denv -> Denv.dty
val add_var : string -> Denv.dty -> denv -> denv

val type_term : denv -> Ptree.lexpr -> term
val type_fmla : denv -> Ptree.lexpr -> fmla

(** error reporting *)

type error

exception Error of error

val report : Format.formatter -> error -> unit

(** export for program typing *)

val specialize_fsymbol : 
  Ptree.qualid -> theory_uc -> lsymbol * Denv.dty list * Denv.dty

