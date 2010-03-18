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

open Ident

(** Types *)

type tvsymbol = private {
  tv_name : ident;
}

module Stv : Set.S with type elt = tvsymbol
module Mtv : Map.S with type key = tvsymbol
module Htv : Hashtbl.S with type key = tvsymbol

val create_tvsymbol : preid -> tvsymbol

(* type symbols and types *)

type tysymbol = private {
  ts_name : ident;
  ts_args : tvsymbol list;
  ts_def  : ty option;
}

and ty = private {
  ty_node : ty_node;
  ty_tag  : int;
}

and ty_node = private
  | Tyvar of tvsymbol
  | Tyapp of tysymbol * ty list

module Sts : Set.S with type elt = tysymbol
module Mts : Map.S with type key = tysymbol
module Hts : Hashtbl.S with type key = tysymbol

exception BadTypeArity
exception NonLinear
exception UnboundTypeVariable

val create_tysymbol : preid -> tvsymbol list -> ty option -> tysymbol

val ty_var : tvsymbol -> ty
val ty_app : tysymbol -> ty list -> ty

val ty_map : (ty -> ty) -> ty -> ty
val ty_fold : ('a -> ty -> 'a) -> 'a -> ty -> 'a
val ty_all : (ty -> bool) -> ty -> bool
val ty_any : (ty -> bool) -> ty -> bool

val ty_s_map : (tysymbol -> tysymbol) -> ty -> ty
val ty_s_fold : ('a -> tysymbol -> 'a) -> 'a -> ty -> 'a
val ty_s_all : (tysymbol -> bool) -> ty -> bool
val ty_s_any : (tysymbol -> bool) -> ty -> bool

exception TypeMismatch

val matching : ty Mtv.t -> ty -> ty -> ty Mtv.t
val ty_match : ty -> ty -> ty Mtv.t -> ty Mtv.t option

(* built-in symbols *)

val ts_int  : tysymbol
val ts_real : tysymbol

val ty_int  : ty
val ty_real : ty

