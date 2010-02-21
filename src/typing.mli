(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Francois Bobot, Jean-Christophe Filliatre,              *)
(*  Johannes Kanig and Andrei Paskevich.                                  *)
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

open Term

(** Typing environments *)

type env

val empty : env

val find_tysymbol : Ptree.ident -> env -> tysymbol
val find_fsymbol : Ptree.ident -> env -> fsymbol
val find_psymbol : Ptree.ident -> env -> psymbol

(** typing *)

val term : env -> Ptree.lexpr -> term
val fmla : env -> Ptree.lexpr -> fmla

(** building environments *)

val add_decl : env -> Ptree.logic_decl -> env
val add_decls : env -> Ptree.logic_decl list -> env

(** error reporting *)

type error

exception Error of error

val report : Format.formatter -> error -> unit
