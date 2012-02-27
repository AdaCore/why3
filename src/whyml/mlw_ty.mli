(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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

open Why3
open Stdlib
open Ident
open Ty
open Term

(** individual types (first-order types w/o effects) *)

type itysymbol = private {
  its_pure : tysymbol;
  its_args : tvsymbol list;
  its_regs : region   list;
  its_def  : ity option;
}

and ity = private {
  ity_node : ity_node;
  ity_tag  : Hashweak.tag;
}

and ity_node = private
  | Ityvar of tvsymbol
  | Itypur of tysymbol * ity list
  | Ityapp of itysymbol * ity list * region list

and region = private {
  reg_name  : ident;
  reg_ity   : ity;
  reg_ghost : bool;
}

module Mits : Map.S with type key = itysymbol
module Sits : Mits.Set
module Hits : Hashtbl.S with type key = itysymbol
module Wits : Hashweak.S with type key = itysymbol

module Mity : Map.S with type key = ity
module Sity : Mity.Set
module Hity : Hashtbl.S with type key = ity
module Wity : Hashweak.S with type key = ity

module Mreg : Map.S with type key = region
module Sreg : Mreg.Set
module Hreg : Hashtbl.S with type key = region
module Wreg : Hashweak.S with type key = region

val its_equal : itysymbol -> itysymbol -> bool
val ity_equal : ity -> ity -> bool

val its_hash : itysymbol -> int
val ity_hash : ity -> int

val reg_equal : region -> region -> bool
val reg_hash : region -> int

exception BadItyArity of itysymbol * int * int
exception BadRegArity of itysymbol * int * int
exception DuplicateRegion of region
exception UnboundRegion of region
exception InvalidRegion of region

val create_region : preid -> ?ghost:bool -> ity -> region

val create_itysymbol :
  preid -> tvsymbol list -> region list -> ity option -> itysymbol

val ity_var : tvsymbol -> ity
val ity_pur : tysymbol -> ity list -> ity

val ity_app : itysymbol -> ity list -> region list -> ity

(* all aliases expanded, all regions removed *)
val ty_of_ity : ity -> ty

(* replaces every [Tyapp] with [Itypur] *)
val ity_of_ty : ty -> ity

(* generic traversal functions *)

val ity_map : (ity -> ity) -> ity -> ity
val ity_fold : ('a -> ity -> 'a) -> 'a -> ity -> 'a
val ity_all : (ity -> bool) -> ity -> bool
val ity_any : (ity -> bool) -> ity -> bool

(* traversal functions on type variables and regions *)

val ity_v_map :
  (tvsymbol -> ity) -> (region -> region) -> ity -> ity

val ity_v_fold :
  ('a -> tvsymbol -> 'a) -> ('a -> region -> 'a) -> 'a -> ity -> 'a

val ity_v_all : (tvsymbol -> bool) -> (region -> bool) -> ity -> bool
val ity_v_any : (tvsymbol -> bool) -> (region -> bool) -> ity -> bool

(** {3 symbol-wise map/fold} *)
(** visits every symbol of the type *)

val ity_s_fold :
  ('a -> itysymbol -> 'a) -> ('a -> tysymbol -> 'a) -> 'a -> ity -> 'a
(*
val ity_s_map : (itysymbol -> itysymbol) -> ity -> ity
val ity_s_all : (itysymbol -> bool) -> ity -> bool
val ity_s_any : (itysymbol -> bool) -> ity -> bool
*)

val ity_freevars : Stv.t -> ity -> Stv.t
val ity_closed : ity -> bool
val ity_pure: ity -> bool

exception RegionMismatch of region * region
exception TypeMismatch of ity * ity

type ity_subst = private {
  ity_subst_tv:  ity Mtv.t;
  ity_subst_reg: region Mreg.t;
}

val ity_subst_empty: ity_subst

val ity_match : ity_subst -> ity -> ity -> ity_subst

val ity_equal_check : ity -> ity -> unit

(** computation types (with effects) *)

(* exception symbols *)
type xsymbol = private {
  xs_name : ident;
  xs_ity:   ity; (* closed and pure *)
}

val create_xsymbol: preid -> ity -> xsymbol

module Mexn: Map.S with type key = xsymbol
module Sexn: Mexn.Set

(* effects *)
type effect = private {
  eff_reads:   Sreg.t;
  eff_writes:  Sreg.t;
  eff_erases:  Sreg.t;
  eff_renames: region Mreg.t; (* if r1->r2 then r1 appears in ty(r2) *)
  eff_raises:  Sexn.t;
}

val eff_empty: effect
val eff_union: effect -> effect -> effect
val eff_read: region -> effect
val eff_write: region -> effect
val eff_erase: region -> effect
val eff_raise: xsymbol -> effect
val eff_remove_raise: xsymbol -> effect -> effect

(* program variables *)
type pvsymbol = private {
  pv_vs:      vsymbol;
  pv_ity:     ity;
  pv_ghost:   bool;
  pv_mutable: region option;
}

val create_pvsymbol: preid -> ?mut:region -> ?ghost:bool -> ity -> pvsymbol

val pv_equal : pvsymbol -> pvsymbol -> bool

(* value types *)
type vty = private
  | VTvalue of pvsymbol
  | VTarrow of pvsymbol * cty

(* computation types *)
and cty = private {
  c_pre: term;
  c_vty: vty;
  c_eff: effect;
  c_post: term;
  c_xpost: xpost;
}

and xpost = (pvsymbol * term) Mexn.t

(* smart constructors *)
val create_cty:
  ?pre:term -> ?post:term -> ?xpost:xpost -> ?effect:effect -> vty -> cty

val vty_value: pvsymbol -> vty
val vty_arrow: pvsymbol -> cty -> vty

