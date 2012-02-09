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

(** value types (w/o effects) *)

type vtysymbol = private {
  vts_pure  : tysymbol;
  vts_args  : tvsymbol list;
  vts_regs  : region   list;
  vts_def   : vty option;
}

and vty = private {
  vty_node : vty_node;
  vty_tag  : Hashweak.tag;
}

and vty_node = private
  | Vtyvar of tvsymbol
  | Vtypur of tysymbol * vty list
  | Vtyapp of vtysymbol * vty list * region list
  (* | Vtymod of tysymbol * vty *)

and region = private {
  reg_ty  : vty;
  reg_tag : Hashweak.tag;
}

module Mvts : Map.S with type key = vtysymbol
module Svts : Mvts.Set
module Hvts : Hashtbl.S with type key = vtysymbol
module Wvts : Hashweak.S with type key = vtysymbol

module Mvty : Map.S with type key = vty
module Svty : Mvty.Set
module Hvty : Hashtbl.S with type key = vty
module Wvty : Hashweak.S with type key = vty

module Mreg : Map.S with type key = region
module Sreg : Mreg.Set
module Hreg : Hashtbl.S with type key = region
module Wreg : Hashweak.S with type key = region

val vts_equal : vtysymbol -> vtysymbol -> bool
val vty_equal : vty -> vty -> bool

val vts_hash : vtysymbol -> int
val vty_hash : vty -> int

val reg_equal : region -> region -> bool
val reg_hash : region -> int

exception BadVtyArity of vtysymbol * int * int
exception BadRegArity of vtysymbol * int * int
exception DuplicateRegion of region
exception UnboundRegion of region
exception InvalidRegion of region

val create_region : vty -> region

val create_vtysymbol :
  preid -> tvsymbol list -> region list -> vty option -> vtysymbol

val vty_var : tvsymbol -> vty
val vty_pur : tysymbol -> vty list -> vty

val vty_app : vtysymbol -> vty list -> region list -> vty

(* erases all [Vtymod] *)
(* val vty_unmod : vty -> vty *)

(* all aliases expanded, all regions removed *)
val ty_of_vty : vty -> ty

(* replaces every [Tyapp] with [Vtypur] *)
val vty_of_ty : ty -> vty

(* generic traversal functions *)

val vty_map : (vty -> vty) -> vty -> vty
val vty_fold : ('a -> vty -> 'a) -> 'a -> vty -> 'a
val vty_all : (vty -> bool) -> vty -> bool
val vty_any : (vty -> bool) -> vty -> bool

(* traversal functions on type variables and regions *)

val vty_v_map :
  (tvsymbol -> vty) -> (region -> region) -> vty -> vty

val vty_v_fold :
  ('a -> tvsymbol -> 'a) -> ('a -> region -> 'a) -> 'a -> vty -> 'a

val vty_v_all : (tvsymbol -> bool) -> (region -> bool) -> vty -> bool
val vty_v_any : (tvsymbol -> bool) -> (region -> bool) -> vty -> bool

(** {3 symbol-wise map/fold} *)
(** visits every symbol of the type *)
(*
val vty_s_map : (vtysymbol -> vtysymbol) -> vty -> vty
val vty_s_fold : ('a -> vtysymbol -> 'a) -> 'a -> vty -> 'a
val vty_s_all : (vtysymbol -> bool) -> vty -> bool
val vty_s_any : (vtysymbol -> bool) -> vty -> bool
*)

val vty_freevars : Stv.t -> vty -> Stv.t
val vty_closed : vty -> bool
val vty_pure: vty -> bool

exception RegionMismatch of region * region
exception TypeMismatch of vty * vty

type vty_subst = private {
  vty_subst_tv:  vty Mtv.t;
  vty_subst_reg: region Mreg.t;
}

val vty_subst_empty: vty_subst

val vty_match : vty_subst -> vty -> vty -> vty_subst

val vty_equal_check : vty -> vty -> unit

(*****

(** computation types (with effects) *)

(* exception symbols *)
type xsymbol = private {
  xs_id : ident;
  xs_vty: vty; (* closed and pure *)
}

val create_xsymbol: preid -> vty -> xsymbol

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
val eff_raise: xsymbol -> effect

val eff_remove_raise: xsymbol -> effect -> effect

(* program symbols *)
type psymbol = private {
  p_vs:      vsymbol;
  p_vty:     vty;
  p_ghost:   bool;
  p_mutable: region option;
}

val create_psymbol: ?mut:region -> ?ghost:bool -> vty -> psymbol

(* expression types *)
type ety = private
  | Evalue of psymbol
  | Earrow of psymbol * cty

(* computation types *)
and cty = private {
  c_pre: fmla;
  c_ety: ety;
  c_eff: effect;
  c_post: fmla;
  c_xpost: xpost;
}

and xpost = (psymbol * fmla) Xmap.t

(* smart constructors *)
val ety_value: psymbol -> ety
val ety_arrow: psymbol -> cty -> ety

val create_cty: ?pre:fmla -> ?post:post -> ?xpost:xpost -> ety -> effect -> cty

****)
