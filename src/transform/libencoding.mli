(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

(* convert a type to a term of type ty_type *)
val term_of_ty : vsymbol Mtv.t -> ty -> term

(* rewrite a closed formula modulo the given free typevars *)
val type_close : Stv.t -> (vsymbol Mtv.t -> 'a -> fmla) -> 'a -> fmla

(* rewrite a closed formula modulo its free typevars *)
val f_type_close : (vsymbol Mtv.t -> fmla -> fmla) -> fmla -> fmla

(* convert a type declaration to a list of lsymbol declarations *)
val lsdecl_of_tydecl : ty_decl list -> decl list

(* monomorphise wrt the base type, the set of kept types, and a symbol map *)
val d_monomorph : ty -> Sty.t -> (lsymbol -> lsymbol) -> decl -> decl list
