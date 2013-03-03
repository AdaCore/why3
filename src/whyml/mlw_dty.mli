(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* destructive types for program type inference *)

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
val add_dvty_vars: tvars -> dvty -> tvars (* add only variables *)

val create_type_variable: unit -> dity
val create_user_type_variable: Ptree.ident -> (* opaque *) bool -> dity
val its_app: itysymbol -> dity list -> dity
val ts_app: tysymbol -> dity list -> dity

val dity_refresh: dity -> dity (* refresh regions *)

val opaque_tvs: Stv.t -> dity -> Stv.t

val is_chainable: dvty -> bool (* non-bool * non-bool -> bool *)

exception DTypeMismatch of dity * dity

val unify: dity -> dity -> unit
val unify_weak: dity -> dity -> unit (* don't unify regions *)

val ity_of_dity: dity -> ity
val vty_of_dvty: dvty -> vty
  (** use with care, only once unification is done *)

val specialize_scheme: tvars -> dvty -> dvty

val specialize_lsymbol: lsymbol -> dvty
val specialize_pvsymbol: pvsymbol -> dity
val specialize_psymbol: psymbol -> dvty
val specialize_plsymbol: plsymbol -> dvty
val specialize_xsymbol: xsymbol -> dity

val print_dity : Format.formatter -> dity -> unit
