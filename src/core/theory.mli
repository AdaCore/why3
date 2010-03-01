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

(** Declarations *)

(* type declaration *)

type ty_def =
  | Tabstract
  | Talgebraic of fsymbol list

type ty_decl = tysymbol * ty_def

(* logic declaration *)

type logic_decl =
  | Lfunction  of fsymbol * (vsymbol list * term) option (* FIXME: binders *)
  | Lpredicate of psymbol * (vsymbol list * fmla) option (* FIXME: binders *)
  | Linductive of psymbol * (ident * fmla) list

(* proposition declaration *)

type prop_kind =
  | Paxiom
  | Plemma
  | Pgoal

type prop_decl = prop_kind * ident * fmla

(* declaration *)

type decl_node =
  | Dtype  of ty_decl list
  | Dlogic of logic_decl list
  | Dprop  of prop_decl

type decl = private {
  d_node : decl_node;
  d_tag  : int;
}

(* smart constructors *)

val create_type : ty_decl list -> decl
val create_logic : logic_decl list -> decl
val create_prop : prop_kind -> preid -> fmla -> decl

(* exceptions *)

exception NotAConstructor of fsymbol
exception IllegalTypeAlias of tysymbol
exception DuplicateVariable of vsymbol
exception UnboundTypeVar of ident
exception UnboundVars of Svs.t

(** Theory *)

module Snm : Set.S with type elt = string
module Mnm : Map.S with type key = string

type theory = private {
  th_name   : ident;
  th_param  : Sid.t;          (* locally declared abstract symbols *)
  th_known  : ident Mid.t;    (* imported and locally declared symbols *)
  th_export : namespace;
  th_decls  : decl_or_use list;
}

and namespace = private {
  ns_ts   : tysymbol Mnm.t;   (* type symbols *)
  ns_fs   : fsymbol Mnm.t;    (* function symbols *)
  ns_ps   : psymbol Mnm.t;    (* predicate symbols *)
  ns_ns   : namespace Mnm.t;  (* inner namespaces *)
  ns_prop : fmla Mnm.t;       (* propositions *)
}

and decl_or_use =
  | Decl of decl
  | Use of theory

(* theory construction *)

type theory_uc  (* a theory under construction *)

val create_theory : preid -> theory_uc

val close_theory : theory_uc -> theory

val open_namespace : theory_uc -> theory_uc

val close_namespace : theory_uc -> string -> import:bool -> theory_uc

val add_decl : theory_uc -> decl -> theory_uc

val use_export : theory_uc -> theory -> theory_uc

type th_inst = {
  inst_ts : tysymbol Mts.t;
  inst_fs : fsymbol  Mfs.t;
  inst_ps : psymbol  Mps.t;
}

val clone_export : theory_uc -> theory -> th_inst -> theory_uc

val get_namespace : theory_uc -> namespace

(* equality *)

val eq : psymbol

(* exceptions *)

exception CloseTheory
exception NoOpenedNamespace
exception RedeclaredIdent of ident
exception CannotInstantiate of ident
exception ClashSymbol of string

(** Debugging *)

val print_th : Format.formatter -> theory_uc -> unit
val print_t  : Format.formatter -> theory  -> unit
