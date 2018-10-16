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
open Ty
open Term
open Decl
open Theory
open Ity
open Expr
open Pdecl

(** *)

type prog_symbol =
  | PV of pvsymbol
  | RS of rsymbol
  | OO of Srs.t

type namespace = {
  ns_ts : itysymbol   Mstr.t;  (* type symbols *)
  ns_ps : prog_symbol Mstr.t;  (* program symbols *)
  ns_xs : xsymbol     Mstr.t;  (* exception symbols *)
  ns_ns : namespace   Mstr.t;  (* inner namespaces *)
}

val ns_find_prog_symbol : namespace -> string list -> prog_symbol

val ns_find_its : namespace -> string list -> itysymbol
val ns_find_pv  : namespace -> string list -> pvsymbol
val ns_find_rs  : namespace -> string list -> rsymbol
val ns_find_xs  : namespace -> string list -> xsymbol
val ns_find_ns  : namespace -> string list -> namespace

type overload =
  | FixedRes of ity (* t -> t -> ... -> T *)
  | SameType        (* t -> t -> ... -> t *)
  | NoOver          (* neither *)

val overload_of_rs : rsymbol -> overload

val ref_attr : Ident.attribute

exception IncompatibleNotation of string

(** {2 Module} *)

type pmodule = private {
  mod_theory : theory;        (* pure theory *)
  mod_units  : mod_unit list; (* module declarations *)
  mod_export : namespace;     (* exported namespace *)
  mod_known  : known_map;     (* known identifiers *)
  mod_local  : Sid.t;         (* locally declared idents *)
  mod_used   : Sid.t;         (* used modules *)
}

and mod_unit =
  | Udecl  of pdecl
  | Uuse   of pmodule
  | Uclone of mod_inst
  | Umeta  of meta * meta_arg list
  | Uscope of string * mod_unit list

and mod_inst = {
  mi_mod : pmodule;
  mi_ty  : ity Mts.t;
  mi_ts  : itysymbol Mts.t;
  mi_ls  : lsymbol Mls.t;
  mi_pr  : prsymbol Mpr.t;
  mi_pk  : prop_kind Mpr.t;
  mi_pv  : pvsymbol Mvs.t;
  mi_rs  : rsymbol Mrs.t;
  mi_xs  : xsymbol Mxs.t;
  mi_df  : prop_kind;
}

val empty_mod_inst: pmodule -> mod_inst

(** {2 Module under construction} *)

type pmodule_uc = private {
  muc_theory : theory_uc;
  muc_units  : mod_unit list;
  muc_import : namespace list;
  muc_export : namespace list;
  muc_known  : known_map;
  muc_local  : Sid.t;
  muc_used   : Sid.t;
  muc_env    : Env.env;
}

val create_module : Env.env -> ?path:string list -> preid -> pmodule_uc
val close_module  : pmodule_uc -> pmodule

val open_scope   : pmodule_uc -> string -> pmodule_uc
val close_scope  : pmodule_uc -> import:bool -> pmodule_uc
val import_scope : pmodule_uc -> string list -> pmodule_uc

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

val clone_export : pmodule_uc -> pmodule -> mod_inst -> pmodule_uc

(** {2 Logic decls} *)

val add_meta : pmodule_uc -> meta -> meta_arg list -> pmodule_uc

(** {2 Program decls} *)

val add_pdecl : ?warn:bool -> vc:bool -> pmodule_uc -> pdecl -> pmodule_uc
(** [add_pdecl ~vc m d] adds declaration [d] in module [m].
    If [vc] is [true], VC is computed and added to [m]. *)

(** {2 Builtin symbols} *)

val builtin_module : pmodule
val bool_module : pmodule
val unit_module : pmodule
val highord_module : pmodule
val tuple_module : int -> pmodule
val ref_module : pmodule

val its_ref     : itysymbol
val ts_ref      : tysymbol
val rs_ref      : rsymbol
val rs_ref_cons : rsymbol
val rs_ref_proj : rsymbol
val ls_ref_cons : lsymbol
val ls_ref_proj : lsymbol

(** {2 WhyML language} *)

open Env

type mlw_file = pmodule Mstr.t

val mlw_language : mlw_file language

val mlw_language_builtin : pathname -> mlw_file

exception ModuleNotFound of pathname * string

val read_module : env -> pathname -> string -> pmodule

(** {2 Pretty-printing} *)

val print_unit : Format.formatter -> mod_unit -> unit
val print_module : Format.formatter -> pmodule -> unit
