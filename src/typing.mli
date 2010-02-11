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

(** typing environments *)

type env

val empty : env

val find_tysymbol : string -> env -> tysymbol
val find_fsymbol : string -> env -> fsymbol
val find_psymbol : string -> env -> psymbol
val find_tyvar : string -> env -> tvsymbol
val find_var : string -> env -> vsymbol

(** typing *)

val term : env -> Ptree.lexpr -> term
val fmla : env -> Ptree.lexpr -> fmla

(** building environments *)

val add : env -> Ptree.logic_decl -> env

(** error reporting *)

type error

exception Error of error

val report : Format.formatter -> error -> unit
