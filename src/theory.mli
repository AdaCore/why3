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

open Ty
open Term

type ty_def = 
  | Ty_abstract
  | Ty_algebraic of fsymbol list

type ty_decl = tysymbol * ty_def 

type logic_decl = 
  | Lfunction  of fsymbol * (vsymbol list * term) option (* FIXME: binders *)
  | Lpredicate of psymbol * (vsymbol list * fmla) option (* FIXME: binders *)
  | Linductive of psymbol * (Name.t * fmla) list

type prop_kind = 
  | Axiom | Lemma | Goal

type decl =
  | Dtype  of ty_decl list
  | Dlogic of logic_decl list
  | Dprop  of prop_kind * Name.t * fmla

type decl_or_use =
  | Decl of decl
  | Use of t

and t = private {
  th_name : Name.t;
  th_namespace : namespace;
  th_decls : decl_or_use list;
}

and namespace

(** Building *)

type th
  (** a theory under construction *)

val create_theory :  Name.t -> th

val open_namespace : th -> Name.t -> import:bool -> th
val close_namespace : th -> th

val use_export : th -> string -> th

type th_inst = {
  inst_ts : tysymbol Mts.t;
  inst_fs : fsymbol  Mfs.t;
  inst_ps : psymbol  Mps.t;
}

val clone_export : th -> string -> th_inst -> th

val add_decl : th -> decl -> th

val close_theory : th -> t

(** Querying *)

val get_namespace : th -> namespace

val find_tysymbol : namespace -> string -> tysymbol
val find_fsymbol  : namespace -> string -> fsymbol
val find_psymbol  : namespace -> string -> psymbol
val find_namespace: namespace -> string -> namespace
val find_fmla     : namespace -> string -> fmla

(** Error reporting *)

type error

exception Error of error

val report : Format.formatter -> error -> unit


(** Debugging *)

val print : Format.formatter -> t -> unit
