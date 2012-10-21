(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Ty
open Term
open Decl
open Theory
open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl

type type_symbol =
  | PT of itysymbol
  | TS of tysymbol

type prog_symbol =
  | PV of pvsymbol
  | PS of psymbol
  | PL of plsymbol
  | XS of xsymbol
  | LS of lsymbol

type namespace = {
  ns_ts : type_symbol Mstr.t;  (* type symbols *)
  ns_ps : prog_symbol Mstr.t;  (* program symbols *)
  ns_ns : namespace   Mstr.t;  (* inner namespaces *)
}

val ns_find_ts : namespace -> string list -> type_symbol
val ns_find_ps : namespace -> string list -> prog_symbol
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

val create_module : Env.env -> ?path:string list -> preid -> module_uc
val close_module  : module_uc -> modul

val open_namespace  : module_uc -> string -> module_uc
val close_namespace : module_uc -> bool -> module_uc

val get_theory : module_uc -> theory_uc
val get_namespace : module_uc -> namespace
val get_known : module_uc -> known_map

val restore_path : ident -> string list * string * string list
(* [restore_path id] returns the triple (library path, module,
   qualified symbol name) if the ident was ever introduced in
   a module declaration. If the ident was declared in several
   different modules, the first association is retained.
   Raises Not_found if the ident was never declared in a module. *)

(** Use and clone *)

val use_export : module_uc -> modul -> module_uc
val clone_export : module_uc -> modul -> th_inst -> module_uc

(** Logic decls *)

val add_decl : module_uc -> decl -> module_uc
val use_export_theory: module_uc -> theory -> module_uc
val clone_export_theory: module_uc -> theory -> th_inst -> module_uc
val add_meta : module_uc -> meta -> meta_arg list -> module_uc

(** Program decls *)

val add_pdecl : wp:bool -> module_uc -> pdecl -> module_uc

exception TooLateInvariant

val add_invariant : module_uc -> itysymbol -> post -> module_uc

(** Builtin symbols *)

val xs_exit : xsymbol (* exception used to break the loops *)
