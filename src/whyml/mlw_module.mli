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
open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl

type prgsymbol =
  | PV of pvsymbol
  | PA of pasymbol
  | PS of psymbol
  | PL of plsymbol

type namespace = private {
  ns_it : itysymbol Mstr.t;  (* type symbols *)
  ns_ps : prgsymbol Mstr.t;  (* program symbols *)
  ns_ns : namespace Mstr.t;  (* inner namespaces *)
}

val ns_find_it : namespace -> string list -> itysymbol
val ns_find_ps : namespace -> string list -> prgsymbol
val ns_find_ns : namespace -> string list -> namespace

(** Module *)

type modul = private {
  mod_theory: theory;			(* pure theory *)
  mod_decls : pdecl list;		(* module declarations *)
  mod_export: namespace;		(* exported namespace *)
  mod_known : known_map;		(* known identifiers *)
  mod_local : Sid.t;			(* locally declared idents *)
  mod_used  : Sid.t;			(* used modules *)
}

(** Module under construction *)

type module_uc (* a module under construction *)

val create_module : ?path:string list -> preid -> module_uc
val close_module  : module_uc -> modul

val open_namespace  : module_uc -> module_uc
val close_namespace : module_uc -> bool -> string option -> module_uc

val get_theory : module_uc -> theory_uc
val get_namespace : module_uc -> namespace
val get_known : module_uc -> known_map

(** Use *)

val use_export : module_uc -> modul -> module_uc

(** Clone *)
val clone_export : module_uc -> modul -> th_inst -> module_uc

(** Logic decls *)

val add_to_theory :
  (theory_uc -> 'a -> theory_uc) -> module_uc -> 'a -> module_uc

val add_decl : module_uc -> decl -> module_uc
val add_decl_with_tuples : module_uc -> decl -> module_uc

val add_ty_decl : module_uc -> tysymbol -> module_uc
val add_data_decl : module_uc -> Decl.data_decl list -> module_uc
val add_param_decl : module_uc -> lsymbol -> module_uc
val add_logic_decl : module_uc -> logic_decl list -> module_uc
val add_ind_decl : module_uc -> ind_decl list -> module_uc
val add_prop_decl : module_uc -> prop_kind -> prsymbol -> term -> module_uc

val use_export_theory: module_uc -> theory -> module_uc
val clone_export_theory: module_uc -> theory -> th_inst -> module_uc
val add_meta : module_uc -> meta -> meta_arg list -> module_uc

(** Program decls *)

val add_pdecl : module_uc -> pdecl -> module_uc
val add_pdecl_with_tuples : module_uc -> pdecl -> module_uc

(*
val add_ty_pdecl : module_uc -> ty_pdecl list -> module_uc
*)
