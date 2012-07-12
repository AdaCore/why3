(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

(* destructive types for program type inference *)

open Why3
open Ident
open Ty
open Term
open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_module

type dreg
type dity
type dvty = dity list * dity (* A -> B -> C == ([A;B],C) *)

type tvars (* a set of type variables *)
val empty_tvars: tvars
val add_dity: tvars -> dity -> tvars
val add_dvty: tvars -> dvty -> tvars

val create_type_variable: unit -> dity
val create_user_type_variable: Ptree.ident -> dity
val its_app: user:bool -> itysymbol -> dity list -> dity
val ts_app: tysymbol -> dity list -> dity

val unify: dity -> dity -> unit
val unify_weak: dity -> dity -> unit (* don't unify regions *)

val ity_of_dity: ?strict:bool -> dity -> ity
val vty_of_dvty: ?strict:bool -> dvty -> vty
  (** use with care, only once unification is done *)

val specialize_scheme: tvars -> dvty -> dvty

val specialize_lsymbol: lsymbol -> dvty
val specialize_pvsymbol: pvsymbol -> dity
val specialize_psymbol: psymbol -> dvty
val specialize_plsymbol: plsymbol -> dvty
val specialize_xsymbol: xsymbol -> dity
