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

open Ty
open Term
open Decl

(* sort symbol of (polymorphic) types *)
val ts_type : tysymbol

(* sort of (polymorphic) types *)
val ty_type : ty

(* ts_type declaration *)
val d_ts_type : decl

(* function symbol mapping ty_type^n to ty_type *)
val ls_of_ts : tysymbol -> lsymbol

(* test whether a function symbol has ty_type as ls_value *)
val is_ls_of_ts : lsymbol -> bool

(* convert a type to a term of type ty_type *)
val term_of_ty : vsymbol Mtv.t -> ty -> term

(* convert a type declaration to a list of lsymbol declarations *)
val lsdecl_of_tydecl : ty_decl list -> decl list

(* sort symbol by default (= undeco) *)
val ts_base : tysymbol

(* sort by default (= undeco) *)
val ty_base : ty

(* ts_base declaration *)
val d_ts_base : decl

(* convert a constant to a functional symbol of type ty_base *)
val ls_of_const : constant -> lsymbol

(* convert a constant to a term of type ty_base *)
val term_of_const : constant -> term

(* monomorphise modulo the set of kept types * and an lsymbol map *)
val d_monomorph : Sty.t -> (lsymbol -> lsymbol) -> decl -> decl list

(* convert tysymbols tagged with meta_kept to a set of types *)
val get_kept_types : Task.tdecl_set -> Sty.t

