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
open Decl

(** Namespace *)

module Snm : Set.S with type elt = string
module Mnm : Map.S with type key = string

type namespace = private {
  ns_ts : tysymbol Mnm.t;   (* type symbols *)
  ns_ls : lsymbol Mnm.t;    (* logic symbols *)
  ns_pr : prop Mnm.t;       (* propositions *)
  ns_ns : namespace Mnm.t;  (* inner namespaces *)
}

val ns_find_ts   : namespace -> string list -> tysymbol
val ns_find_ls   : namespace -> string list -> lsymbol
val ns_find_pr   : namespace -> string list -> prsymbol

val ns_find_prop : namespace -> string list -> prop
val ns_find_fmla : namespace -> string list -> fmla

(** Theory *)

type theory = private {
  th_name   : ident;        (* theory name *)
  th_decls  : tdecl list;   (* theory declarations *)
  th_export : namespace;    (* exported namespace *)
  th_known  : known_map;    (* known identifiers *)
  th_clone  : clone_map;    (* cloning history *)
  th_used   : use_map;      (* referenced theories *)
  th_local  : Sid.t;        (* locally declared idents *)
}

and tdecl = private
  | Decl  of decl
  | Use   of theory
  | Clone of theory * (ident * ident) list

and use_map = theory Mid.t

and clone_map = Sid.t Mid.t

val builtin_theory : theory

(** Constructors and utilities *)

type theory_uc  (* a theory under construction *)

val create_theory : preid -> theory_uc
val close_theory  : theory_uc -> theory

val add_decl : theory_uc -> decl -> theory_uc
val use_export : theory_uc -> theory -> theory_uc
val merge_used : use_map -> theory -> use_map

val open_namespace  : theory_uc -> theory_uc
val close_namespace : theory_uc -> bool -> string option -> theory_uc

val get_namespace : theory_uc -> namespace

(** Declaration constructors + add_decl *)

val add_ty_decl : theory_uc -> ty_decl list -> theory_uc
val add_logic_decl : theory_uc -> logic_decl list -> theory_uc
val add_ind_decl : theory_uc -> ind_decl list -> theory_uc
val add_prop_decl : theory_uc -> prop_kind -> prsymbol -> fmla -> theory_uc

val add_ty_decls : theory_uc -> ty_decl list -> theory_uc
val add_logic_decls : theory_uc -> logic_decl list -> theory_uc
val add_ind_decls : theory_uc -> ind_decl list -> theory_uc

(** Clone *)

type th_inst = {
  inst_ts    : tysymbol Mts.t; (* old to new *)
  inst_ls    : lsymbol  Mls.t;
  inst_lemma : Spr.t;
  inst_goal  : Spr.t;
}

val empty_inst : th_inst

val create_inst :
  ts    : (tysymbol * tysymbol) list ->
  ls    : (lsymbol  * lsymbol)  list ->
  lemma : prsymbol list ->
  goal  : prsymbol list -> th_inst

val clone_theory : ('a -> tdecl -> 'a) -> 'a -> theory -> th_inst -> 'a
val clone_export : theory_uc -> theory -> th_inst -> theory_uc
val merge_clone  : clone_map -> theory -> (ident * ident) list -> clone_map
val cloned_from  : clone_map -> ident -> ident -> bool

(* exceptions *)

exception NonLocal of ident
exception CannotInstantiate of ident
exception BadInstance of ident * ident

exception CloseTheory
exception NoOpenedNamespace
exception ClashSymbol of string

