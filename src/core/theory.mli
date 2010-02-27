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
open Ty
open Term

type ty_def = 
  | Ty_abstract
  | Ty_algebraic of fsymbol list

type ty_decl = tysymbol * ty_def 

type logic_decl = 
  | Lfunction  of fsymbol * (vsymbol list * term) option (* FIXME: binders *)
  | Lpredicate of psymbol * (vsymbol list * fmla) option (* FIXME: binders *)
  | Linductive of psymbol * (ident * fmla) list

type prop_kind = 
  | Axiom | Lemma | Goal

type decl_node =
  | Dtype  of ty_decl list
  | Dlogic of logic_decl list
  | Dprop  of prop_kind * ident * fmla

type decl = private {d_node : decl_node; d_tag : int}

type decl_or_use =
  | Decl of decl
  | Use of theory

and theory = private {
  th_name   : ident;
  th_param  : Sid.t;           (* locally declared abstract symbols *)
  th_known  : ident Mid.t;     (* imported and locally declared symbols *)
  th_export : namespace;
  th_decls  : decl_or_use list;
}

and namespace

(** Building *)

type theory_uc
  (** a theory under construction *)

val create_theory : ident -> theory_uc

val open_namespace : theory_uc -> theory_uc
val close_namespace : theory_uc -> ident -> import:bool -> theory_uc

val use_export : theory_uc -> theory -> theory_uc

type th_inst = {
  inst_ts : tysymbol Mts.t;
  inst_fs : fsymbol  Mfs.t;
  inst_ps : psymbol  Mps.t;
}

val clone_export : theory_uc -> theory -> th_inst -> theory_uc

val add_decl : theory_uc -> decl_node -> theory_uc

val close_theory : theory_uc -> theory

(** Querying *)

val get_namespace : theory_uc -> namespace

val find_tysymbol : namespace -> string -> tysymbol
val find_fsymbol  : namespace -> string -> fsymbol
val find_psymbol  : namespace -> string -> psymbol
val find_namespace: namespace -> string -> namespace
val find_prop     : namespace -> string -> fmla

val mem_tysymbol : namespace -> string -> bool
val mem_fsymbol  : namespace -> string -> bool
val mem_psymbol  : namespace -> string -> bool
val mem_namespace: namespace -> string -> bool
val mem_prop     : namespace -> string -> bool

(** Exceptions *)

exception CloseTheory
exception NoOpenedNamespace
exception RedeclaredIdent of ident
exception CannotInstantiate
exception ClashSymbol of string


(** Debugging *)

val print_th : Format.formatter -> theory_uc -> unit
val print_t  : Format.formatter -> theory  -> unit
