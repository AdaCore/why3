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

(** region variables *)

type rvsymbol = private {
  rv_name : ident;
}

module Mrv : Map.S with type key = rvsymbol
module Srv : Mrv.Set
module Hrv : Hashtbl.S with type key = rvsymbol
module Wrv : Hashweak.S with type key = rvsymbol

val rv_equal : rvsymbol -> rvsymbol -> bool

val rv_hash : rvsymbol -> int

val create_rvsymbol : preid -> rvsymbol

(** subregion projections *)

type srsymbol = private {
  srs_name : ident;
}

val srs_equal : srsymbol -> srsymbol -> bool

val srs_hash : srsymbol -> int

val create_srsymbol : preid -> srsymbol

(** regions *)

type region = private {
  reg_node : reg_node;
  reg_tag  : Hashweak.tag;
}

and reg_node = private
  | Rvar of rvsymbol
  | Rsub of srsymbol * region

val reg_equal : region -> region -> bool

val reg_hash : region -> int

module Mreg : Map.S with type key = region
module Sreg : Mreg.Set
module Hreg : Hashtbl.S with type key = region
module Wreg : Hashweak.S with type key = region

val reg_var : rvsymbol -> region
val reg_sub : srsymbol -> region -> region

val reg_getrv : region -> rvsymbol

(** value types (w/o effects) *)

type vtysymbol = private {
  vts_pure  : tysymbol;
  vts_args  : tvsymbol list;
  vts_regs  : rvsymbol list;
  vts_def   : vty option;
  vts_model : bool;
}

and vty = private {
  vty_node : vty_node;
  vty_tag  : Hashweak.tag;
}

and vty_node = private
  | Vtyvar of tvsymbol
  | Vtypur of tysymbol * vty list
  | Vtyapp of vtysymbol * vty list * region list

module Mvts : Map.S with type key = vtysymbol
module Svts : Mvts.Set
module Hvts : Hashtbl.S with type key = vtysymbol
module Wvts : Hashweak.S with type key = vtysymbol

module Mvty : Map.S with type key = vty
module Svty : Mvty.Set
module Hvty : Hashtbl.S with type key = vty
module Wvty : Hashweak.S with type key = vty

val vts_equal : vtysymbol -> vtysymbol -> bool
val vty_equal : vty -> vty -> bool

val vts_hash : vtysymbol -> int
val vty_hash : vty -> int

exception BadVtyArity of vtysymbol * int * int
exception BadRegArity of vtysymbol * int * int
exception DuplicateRegVar of rvsymbol
exception UnboundRegVar of rvsymbol
exception InvalidRegion of region

val create_vtysymbol :
  preid -> tvsymbol list -> rvsymbol list -> vty option -> bool -> vtysymbol

val vty_var : tvsymbol -> vty
val vty_pur : tysymbol -> vty list -> vty
val vty_app : vtysymbol -> vty list -> region list -> vty
val vty_app_model : vtysymbol -> vty list -> region list -> vty

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

(*
(** {3 symbol-wise map/fold} *)
(** visits every symbol of the type *)
val ty_s_map : (tysymbol -> tysymbol) -> ty -> ty
val ty_s_fold : ('a -> tysymbol -> 'a) -> 'a -> ty -> 'a
val ty_s_all : (tysymbol -> bool) -> ty -> bool
val ty_s_any : (tysymbol -> bool) -> ty -> bool

exception TypeMismatch of ty * ty

val ty_match : ty Mrv.t -> ty -> ty -> ty Mrv.t
val ty_inst  : ty Mrv.t -> ty -> ty
val ty_freevars : Srv.t -> ty -> Srv.t
val ty_closed : ty -> bool

val ty_equal_check : ty -> ty -> unit
*)


