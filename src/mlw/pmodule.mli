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

open Wstdlib
open Ident
open Theory
open Ity
open Expr
open Pdecl

(** *)

type prog_symbol =
  | PV of pvsymbol
  | RS of rsymbol
  | XS of xsymbol

type namespace = {
  ns_ts : itysymbol   Mstr.t;  (* type symbols *)
  ns_ps : prog_symbol Mstr.t;  (* program symbols *)
  ns_ns : namespace   Mstr.t;  (* inner namespaces *)
}

val ns_find_its : namespace -> string list -> itysymbol

val ns_find_prog_symbol : namespace -> string list -> prog_symbol

val ns_find_pv  : namespace -> string list -> pvsymbol
val ns_find_rs  : namespace -> string list -> rsymbol
val ns_find_xs  : namespace -> string list -> xsymbol

val ns_find_ns  : namespace -> string list -> namespace

(** {2 Module} *)

type pmodule = private {
  mod_theory : theory;      (* pure theory *)
  mod_decls  : pdecl list;  (* module declarations *)
  mod_export : namespace;   (* exported namespace *)
  mod_known  : known_map;   (* known identifiers *)
  mod_local  : Sid.t;       (* locally declared idents *)
  mod_used   : Sid.t;       (* used modules *)
}

(** {2 Module under construction} *)

type pmodule_uc = private {
  muc_theory : theory_uc;
  muc_name   : string;
  muc_path   : string list;
  muc_decls  : pdecl list;
  muc_prefix : string list;
  muc_import : namespace list;
  muc_export : namespace list;
  muc_known  : known_map;
  muc_local  : Sid.t;
  muc_used   : Sid.t;
  muc_env    : Env.env option;
}

val create_module : Env.env -> ?path:string list -> preid -> pmodule_uc
val close_module  : pmodule_uc -> pmodule

val open_namespace  : pmodule_uc -> string -> pmodule_uc
val close_namespace : pmodule_uc -> import:bool -> pmodule_uc

val restore_path : ident -> string list * string * string list
(** [restore_path id] returns the triple (library path, module,
   qualified symbol name) if the ident was ever introduced in
   a module declaration. If the ident was declared in several
   different modules, the first association is retained.
   If [id] is a module name, the third component is an empty list.
   Raises Not_found if the ident was never declared in/as a module. *)

val restore_module : theory -> pmodule
(** retrieves a module from its underlying theory
    raises [Not_found] if no such module exists *)

(** {2 Use and clone} *)

val use_export : pmodule_uc -> pmodule -> pmodule_uc

(** {2 Logic decls} *)

val add_meta : pmodule_uc -> meta -> meta_arg list -> pmodule_uc

(** {2 Program decls} *)

val add_pdecl : wp:bool -> pmodule_uc -> pdecl -> pmodule_uc
(** [add_pdecl ~wp m d] adds declaration [d] in module [m].
    If [wp] is [true], VC is computed and added to [m]. *)

(** {2 Builtin symbols} *)

val builtin_module : pmodule

val bool_module : pmodule

(* TODO
val unit_module : pmodule
*)

val highord_module : pmodule

val tuple_module : int -> pmodule

val tuple_module_name : string -> int option

val add_pdecl_with_tuples : pmodule_uc -> pdecl -> pmodule_uc

(** {2 WhyML language} *)

open Env

type mlw_file = pmodule Mstr.t * theory Mstr.t

val mlw_language : mlw_file language

exception ModuleNotFound of pathname * string

val read_module : env -> pathname -> string -> pmodule
