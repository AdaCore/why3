(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {1 Program modules} *)

open Wstdlib
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

val ns_find_type_symbol : namespace -> string list -> type_symbol
val ns_find_prog_symbol : namespace -> string list -> prog_symbol

val ns_find_its : namespace -> string list -> itysymbol
val ns_find_ts  : namespace -> string list -> tysymbol
val ns_find_pv  : namespace -> string list -> pvsymbol
val ns_find_ps  : namespace -> string list -> psymbol
val ns_find_pl  : namespace -> string list -> plsymbol
val ns_find_xs  : namespace -> string list -> xsymbol
val ns_find_ls  : namespace -> string list -> lsymbol

val ns_find_ns  : namespace -> string list -> namespace

(** {2 Module} *)

type modul = private {
  mod_theory: theory;			(* pure theory *)
  mod_decls : pdecl list;		(* module declarations *)
  mod_export: namespace;		(* exported namespace *)
  mod_known : Mlw_decl.known_map;	(* known identifiers *)
  mod_local : Sid.t;			(* locally declared idents *)
  mod_used  : Sid.t;			(* used modules *)
}

(** {2 Module under construction} *)

type module_uc (* a module under construction *)

val create_module : Env.env -> ?path:string list -> preid -> module_uc
val close_module  : module_uc -> modul

val open_namespace  : module_uc -> string -> module_uc
val close_namespace : module_uc -> bool -> module_uc

val get_theory : module_uc -> theory_uc
val get_namespace : module_uc -> namespace
val get_known : module_uc -> Mlw_decl.known_map

val restore_path : ident -> string list * string * string list
(** [restore_path id] returns the triple (library path, module,
   qualified symbol name) if the ident was ever introduced in
   a module declaration. If the ident was declared in several
   different modules, the first association is retained.
   If [id] is a module name, the third component is an empty list.
   Raises Not_found if the ident was never declared in/as a module. *)

val restore_module : theory -> modul
(** retrieves a module from its underlying theory
    raises [Not_found] if no such module exists *)

(** {2 Use and clone} *)

val use_export : module_uc -> modul -> module_uc

type mod_inst = {
  inst_pv : pvsymbol Mpv.t;
  inst_ps : psymbol Mps.t;
}

val clone_export : module_uc -> modul -> mod_inst -> th_inst -> module_uc

(** {2 Logic decls} *)

val add_decl : module_uc -> decl -> module_uc
val use_export_theory: module_uc -> theory -> module_uc
val clone_export_theory: module_uc -> theory -> th_inst -> module_uc
val add_meta : module_uc -> meta -> meta_arg list -> module_uc

(** {2 Program decls} *)

val add_pdecl : wp:bool -> module_uc -> pdecl -> module_uc
(** [add_pdecl ~wp m d] adds declaration [d] in module [m].
    If [wp] is [true], VC is computed and added to [m]. *)

exception TooLateInvariant

val add_invariant : module_uc -> itysymbol -> post -> module_uc

(** {2 Builtin symbols} *)

val xs_exit : xsymbol (* exception used to break the loops *)

(** {2 WhyML language} *)

open Env

type mlw_file = modul Mstr.t * theory Mstr.t

val mlw_language : mlw_file language

exception ModuleNotFound of pathname * string
exception ModuleOrTheoryNotFound of pathname * string

type module_or_theory = Module of modul | Theory of theory

val read_module : env -> pathname -> string -> modul
val read_module_or_theory : env -> pathname -> string -> module_or_theory
