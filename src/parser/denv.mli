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
open Ty
open Term
open Theory

(** Destructive unification *)

type type_var

type dty = 
  | Tyvar of type_var
  | Tyapp of tysymbol * dty list

val create_ty_decl_var : ?loc:Ptree.loc -> user:bool -> tvsymbol -> type_var

val unify : dty -> dty -> bool

val print_dty : Format.formatter -> dty -> unit

val ty_of_dty : dty -> ty

(** Specialization *)

val specialize_tysymbol : 
  loc:Ptree.loc -> tysymbol -> type_var list

val specialize_lsymbol  : 
  loc:Ptree.loc -> lsymbol -> dty list * dty option


(** Error reporting *)

type error

exception Error of error

val report : Format.formatter -> error -> unit

