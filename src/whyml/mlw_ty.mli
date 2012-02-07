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
  | Vtymod of tysymbol * vty

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
  preid -> tvsymbol list -> region list -> vty option -> bool -> vtysymbol

val vty_var : tvsymbol -> vty
val vty_pur : tysymbol -> vty list -> vty

val vty_app : vtysymbol -> vty list -> region list -> vty

(* erases all [Vtymod] *)
val vty_unmod : vty -> vty

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

exception TypeMismatch of vty * vty

val vty_match : vty Mreg.t -> vty -> vty -> vty Mreg.t
val vty_inst  : vty Mreg.t -> vty -> vty
val vty_freevars : Srv.t -> vty -> Srv.t
val vty_closed : vty -> bool

val vty_equal_check : vty -> vty -> unit
*)


