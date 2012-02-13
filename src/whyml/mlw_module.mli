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
open Util
open Ident
open Ty
open Theory
open Mlw_ty
open Mlw_expr
open Mlw_decl

type namespace = private {
  ns_it : itysymbol Mstr.t;  (* type symbols *)
  ns_ps : psymbol Mstr.t;    (* program symbols *)
  ns_ns : namespace Mstr.t;  (* inner namespaces *)
}

val ns_find_it : namespace -> string list -> itysymbol
val ns_find_ps : namespace -> string list -> psymbol
val ns_find_ns : namespace -> string list -> namespace

(** Module *)

type modul = private {
  mod_theory: theory;			(* pure theory *)
  mod_decls : pdecl list;		(* module declarations *)
  mod_export: namespace;		(* exported namespace *)
  mod_known : known_map;		(* known identifiers *)
  mod_local : Sid.t;			(* locally declared idents *)
}

(** Module under construction *)

type module_uc (* a module under construction *)

val create_module : ?path:string list -> preid -> module_uc
val close_module  : module_uc -> modul

val open_namespace  : module_uc -> module_uc
val close_namespace : module_uc -> bool -> string option -> module_uc

val get_namespace : module_uc -> namespace
val get_known : module_uc -> known_map

(** Use *)

(* val use_export : module_uc -> modul -> module_uc *)

(** Clone: not yet implemented *)
