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

open Why3
open Stdlib
open Ident
open Ty
open Term

(** individual types (first-order types w/o effects) *)

module rec T : sig

  type varset = private {
    vars_tv  : Stv.t;
    vars_reg : Mreg.Set.t;
  }

  type itysymbol = private {
    its_pure : tysymbol;
    its_args : tvsymbol list;
    its_regs : region   list;
    its_def  : ity option;
    its_abst : bool;
    its_priv : bool;
  }

  and ity = private {
    ity_node : ity_node;
    ity_vars : varset;
    ity_tag  : Hashweak.tag;
  }

  and ity_node = private
    | Ityvar of tvsymbol
    | Itypur of tysymbol * ity list
    | Ityapp of itysymbol * ity list * region list

  and region = private {
    reg_name  : ident;
    reg_ity   : ity;
  }

end
and Mreg : sig include Map.S with type key = T.region end

open T

module Mits : Map.S with type key = itysymbol
module Sits : Mits.Set
module Hits : Hashtbl.S with type key = itysymbol
module Wits : Hashweak.S with type key = itysymbol

module Mity : Map.S with type key = ity
module Sity : Mity.Set
module Hity : Hashtbl.S with type key = ity
module Wity : Hashweak.S with type key = ity

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

val create_region : preid -> ity -> region

val create_itysymbol : preid -> ?abst:bool -> ?priv:bool ->
  tvsymbol list -> region list -> ity option -> itysymbol

val ity_var : tvsymbol -> ity
val ity_pur : tysymbol -> ity list -> ity

val ity_app : itysymbol -> ity list -> region list -> ity
val ity_app_fresh : itysymbol -> ity list -> ity

(* all aliases expanded, all regions removed *)
val ty_of_ity : ity -> ty

(* replaces every [Tyapp] with [Itypur] *)
val ity_of_ty : ty -> ity

(* generic traversal functions *)

val ity_map : (ity -> ity) -> ity -> ity
val ity_fold : ('a -> ity -> 'a) -> 'a -> ity -> 'a
val ity_all : (ity -> bool) -> ity -> bool
val ity_any : (ity -> bool) -> ity -> bool

(* traversal functions on type symbols *)

val ity_s_fold :
  ('a -> itysymbol -> 'a) -> ('a -> tysymbol -> 'a) -> 'a -> ity -> 'a

val ity_s_all : (itysymbol -> bool) -> (tysymbol -> bool) -> ity -> bool
val ity_s_any : (itysymbol -> bool) -> (tysymbol -> bool) -> ity -> bool

(* traversal functions on type variables and regions *)

val ity_v_map : (tvsymbol -> ity) -> (region -> region) -> ity -> ity

val ity_v_fold :
  ('a -> tvsymbol -> 'a) -> ('a -> region -> 'a) -> 'a -> ity -> 'a

val ity_v_all : (tvsymbol -> bool) -> (region -> bool) -> ity -> bool
val ity_v_any : (tvsymbol -> bool) -> (region -> bool) -> ity -> bool

val ity_closed : ity -> bool
val ity_pure : ity -> bool

val ts_unit : tysymbol
val ty_unit : ty

val ity_int : ity
val ity_bool : ity
val ity_unit : ity

exception RegionMismatch of region * region
exception TypeMismatch of ity * ity

type ity_subst = private {
  ity_subst_tv  : ity Mtv.t;
  ity_subst_reg : region Mreg.t;
}

val ity_subst_empty : ity_subst

val ity_match : ity_subst -> ity -> ity -> ity_subst

val reg_match : ity_subst -> region -> region -> ity_subst

val ity_equal_check : ity -> ity -> unit

val ity_subst_union : ity_subst -> ity_subst -> ity_subst

val ity_full_inst : ity_subst -> ity -> ity

val reg_full_inst : ity_subst -> region -> region

val vars_empty : varset

val vars_union : varset -> varset -> varset

val vars_freeze : varset -> ity_subst

val create_varset : Stv.t -> Sreg.t -> varset

(* exception symbols *)
type xsymbol = private {
  xs_name : ident;
  xs_ity  : ity; (* closed and pure *)
}

val xs_equal : xsymbol -> xsymbol -> bool

val create_xsymbol : preid -> ity -> xsymbol

module Mexn: Map.S with type key = xsymbol
module Sexn: Mexn.Set

(* effects *)
type effect = private {
  eff_reads  : Sreg.t;
  eff_writes : Sreg.t;
  eff_raises : Sexn.t;
  eff_ghostr : Sreg.t; (* ghost reads *)
  eff_ghostw : Sreg.t; (* ghost writes *)
  eff_ghostx : Sexn.t; (* ghost raises *)
  (* if r1 -> Some r2 then r1 appears in ty(r2) *)
  eff_resets : region option Mreg.t;
}

val eff_empty : effect
val eff_union : effect -> effect -> effect
val eff_ghostify : effect -> effect

val eff_read  : effect -> ?ghost:bool -> region -> effect
val eff_write : effect -> ?ghost:bool -> region -> effect
val eff_raise : effect -> ?ghost:bool -> xsymbol -> effect
val eff_reset : effect -> region -> effect

val eff_assign : effect -> ?ghost:bool -> region -> ity -> effect

val eff_remove_raise : effect -> xsymbol -> effect

val eff_full_inst : ity_subst -> effect -> effect

val eff_filter : varset -> effect -> effect

val eff_is_empty : effect -> bool

(** program types *)

(* type of function arguments and values *)
type vty_value = private {
  vtv_ity   : ity;
  vtv_ghost : bool;
  vtv_mut   : region option;
  vtv_vars  : varset;
}

type vty =
  | VTvalue of vty_value
  | VTarrow of vty_arrow

and vty_arrow = private {
  vta_arg    : vty_value;
  vta_result : vty;
  vta_effect : effect;
  vta_ghost  : bool;
  vta_vars   : varset;
  (* this varset covers every type variable and region in vta_arg
     and vta_result, but may skip some type variables and regions
     in vta_effect *)
}

(* smart constructors *)

val vty_value : ?ghost:bool -> ?mut:region -> ity -> vty_value

val vty_arrow : vty_value -> ?effect:effect -> ?ghost:bool -> vty -> vty_arrow

val vty_app_arrow : vty_arrow -> vty_value -> effect * vty

val vty_vars : varset -> vty -> varset

val vty_ghost : vty -> bool
val vty_ghostify : vty -> vty

(* the substitution must cover not only vta.vta_tvs and vta.vta_regs
   but also every type variable and every region in vta_effect *)
val vta_full_inst : ity_subst -> vty_arrow -> vty_arrow

(* remove from the given arrow every effect that is covered
   neither by the arrow's vta_vars nor by the given varset *)
val vta_filter : varset -> vty_arrow -> vty_arrow

(** THE FOLLOWING CODE MIGHT BE USEFUL LATER FOR WPgen *)
(*
(* program variables *)
type pvsymbol = private {
  pv_vs      : vsymbol;
  pv_ity     : ity;
  pv_ghost   : bool;
  pv_mutable : region option;
  pv_tvs     : Stv.t;
  pv_regs    : Sreg.t;
}

val create_pvsymbol : preid -> ?mut:region -> ?ghost:bool -> ity -> pvsymbol

val pv_equal : pvsymbol -> pvsymbol -> bool

(* value types *)

type pre   = term (* precondition *)
type post  = term (* postcondition *)
type xpost = (vsymbol * post) Mexn.t (* exceptional postconditions *)

type vty_arrow  (* pvsymbol -> vty_comp *)

type vty = private
  | VTvalue of pvsymbol
  | VTarrow of vty_arrow

type vty_comp = private {
  c_vty   : vty;
  c_eff   : effect;
  c_pre   : pre;
  c_post  : post;
  c_xpost : xpost;
}

(* smart constructors *)
val vty_value : pvsymbol -> vty

val vty_arrow : pvsymbol ->
  ?pre:term -> ?post:term -> ?xpost:xpost -> ?effect:effect -> vty -> vty

val vty_app_arrow : vty_arrow -> pvsymbol -> vty_comp

val open_vty_arrow : vty_arrow -> pvsymbol * vty

val vty_freevars : Stv.t -> vty -> Stv.t (* only args and values count... *)
val vty_topregions : Sreg.t -> vty -> Sreg.t (* ...not eff/pre/post/xpost *)

(* the substitution must cover not only the vty_freevars and
   vty_topregions of vty, but also every type variable and
   every region in effects and pre/post/xpost formulas *)
val vty_full_inst : ity_subst -> vty -> vty
*)
