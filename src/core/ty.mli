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

type tvsymbol = ident

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

exception NonLinear
exception UnboundTypeVariable

val create_tvsymbol : preid -> tvsymbol
val create_tysymbol : preid -> tvsymbol list -> ty option -> tysymbol

module Sts : Set.S with type elt = tysymbol
module Mts : Map.S with type key = tysymbol
module Hts : Hashtbl.S with type key = tysymbol

exception BadTypeArity

val ty_var : tvsymbol -> ty
val ty_app : tysymbol -> ty list -> ty

val ty_map : (ty -> ty) -> ty -> ty
val ty_fold : ('a -> ty -> 'a) -> 'a -> ty -> 'a
val ty_forall : (ty -> bool) -> ty -> bool
val ty_exists : (ty -> bool) -> ty -> bool

val ty_s_map : (tysymbol -> tysymbol) -> ty -> ty
val ty_s_fold : ('a -> tysymbol -> 'a) -> 'a -> ty -> 'a
val ty_s_forall : (tysymbol -> bool) -> ty -> bool
val ty_s_exists : (tysymbol -> bool) -> ty -> bool

exception TypeMismatch

val matching : ty Mid.t -> ty -> ty -> ty Mid.t
val ty_match : ty -> ty -> ty Mid.t -> ty Mid.t option

(* built-in symbols *)

val ts_int  : tysymbol
val ts_real : tysymbol

val ty_int  : ty
val ty_real : ty

