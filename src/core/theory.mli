(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib

(** Theories and Namespaces *)

open Ident
open Ty
open Term
open Decl

type namespace = {
  ns_ts : tysymbol Mstr.t;   (* type symbols *)
  ns_ls : lsymbol Mstr.t;    (* logic symbols *)
  ns_pr : prsymbol Mstr.t;   (* propositions *)
  ns_ns : namespace Mstr.t;  (* inner namespaces *)
}

val empty_ns : namespace

val ns_find_ts : namespace -> string list -> tysymbol
val ns_find_ls : namespace -> string list -> lsymbol
val ns_find_pr : namespace -> string list -> prsymbol
val ns_find_ns : namespace -> string list -> namespace

(** {2 Meta properties} *)

type meta_arg_type =
  | MTty
  | MTtysymbol
  | MTlsymbol
  | MTprsymbol
  | MTstring
  | MTint

type meta_arg =
  | MAty  of ty
  | MAts  of tysymbol
  | MAls  of lsymbol
  | MApr  of prsymbol
  | MAstr of string
  | MAint of int

type meta = private {
  meta_name : string;
  meta_type : meta_arg_type list;
  meta_excl : bool;
  meta_desc : Pp.formatted;
  meta_tag  : int;
}

val print_meta_desc : Pp.formatter -> meta -> unit

module Mmeta : Extmap.S with type key = meta
module Smeta : Extset.S with module M = Mmeta
module Hmeta : Exthtbl.S with type key = meta

val meta_equal : meta -> meta -> bool
val meta_hash : meta -> int

val register_meta :
  desc:Pp.formatted -> string -> meta_arg_type list -> meta

val register_meta_excl :
  desc:Pp.formatted -> string -> meta_arg_type list -> meta
(** With exclusive metas, each new meta cancels the previous one.
    Useful for transformation or printer parameters *)

val lookup_meta : string -> meta
val list_metas  : unit -> meta list

val meta_range : meta
val meta_float : meta

(** {2 Theories} *)

type theory = private {
  th_name   : ident;      (* theory name *)
  th_path   : string list;(* environment qualifiers *)
  th_decls  : tdecl list; (* theory declarations *)
  th_export : namespace;  (* exported namespace *)
  th_known  : known_map;  (* known identifiers *)
  th_local  : Sid.t;      (* locally declared idents *)
  th_used   : Sid.t;      (* used theories *)
}

and tdecl = private {
  td_node : tdecl_node;
  td_tag  : int;
}

and tdecl_node = private
  | Decl  of decl
  | Use   of theory
  | Clone of theory * symbol_map
  | Meta  of meta * meta_arg list

and symbol_map = private {
  sm_ts : tysymbol Mts.t;
  sm_ls : lsymbol Mls.t;
  sm_pr : prsymbol Mpr.t;
}

module Mtdecl : Extmap.S with type key = tdecl
module Stdecl : Extset.S with module M = Mtdecl
module Htdecl : Exthtbl.S with type key = tdecl

val td_equal : tdecl -> tdecl -> bool
val td_hash : tdecl -> int

(** {2 Constructors and utilities} *)

type theory_uc  (** a theory under construction *)

val create_theory : ?path:string list -> preid -> theory_uc
val close_theory  : theory_uc -> theory

val open_namespace  : theory_uc -> string -> theory_uc
val close_namespace : theory_uc -> bool (* import *) -> theory_uc

val get_namespace : theory_uc -> namespace
val get_known : theory_uc -> known_map
val get_rev_decls : theory_uc -> tdecl list

val restore_path : ident -> string list * string * string list
(** [restore_path id] returns the triple (library path, theory,
   qualified symbol name) if the ident was ever introduced in
   a theory declaration. If the ident was declared in several
   different theories, the first association is retained.
   If [id] is a theory name, the third component is an empty list.
   Raises [Not_found] if the ident was never declared in/as a theory. *)

(** {2 Declaration constructors} *)

val create_decl : decl -> tdecl

val add_decl : ?warn:bool -> theory_uc -> decl -> theory_uc

val add_ty_decl : theory_uc -> tysymbol -> theory_uc
val add_data_decl : theory_uc -> data_decl list -> theory_uc
val add_param_decl : theory_uc -> lsymbol -> theory_uc
val add_logic_decl : theory_uc -> logic_decl list -> theory_uc
val add_ind_decl : theory_uc -> ind_sign -> ind_decl list -> theory_uc
val add_prop_decl :
  ?warn:bool -> theory_uc -> prop_kind -> prsymbol -> term -> theory_uc

(** {2 Use} *)

val create_use : theory -> tdecl
val use_export : theory_uc -> theory -> theory_uc

(** {2 Clone} *)

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

val warn_clone_not_abstract : Loc.position -> theory -> unit

val clone_theory : ('a -> tdecl -> 'a) -> 'a -> theory -> th_inst -> 'a

val clone_export : theory_uc -> theory -> th_inst -> theory_uc

val create_null_clone : theory -> tdecl

val is_empty_sm : symbol_map -> bool

(** {2 Meta} *)

val create_meta : meta -> meta_arg list -> tdecl

val add_meta : theory_uc -> meta -> meta_arg list -> theory_uc

val clone_meta : tdecl -> symbol_map -> tdecl
(** [clone_meta td_meta sm] produces from [td_meta]
    a new Meta tdecl instantiated with respect to [sm]. *)

(*
val on_meta: meta-> ('a -> meta_arg list -> 'a) -> 'a -> theory -> 'a
*)

(** {2 Base theories} *)

val builtin_theory : theory

val bool_theory : theory

val unit_theory : theory

val highord_theory : theory

val tuple_theory : int -> theory

val tuple_theory_name : string -> int option

val add_decl_with_tuples : theory_uc -> decl -> theory_uc

(* {2 Exceptions} *)

exception NonLocal of ident
exception CannotInstantiate of ident
exception BadInstance of ident * ident

exception CloseTheory
exception NoOpenedNamespace
exception ClashSymbol of string

exception KnownMeta of meta
exception UnknownMeta of string
exception BadMetaArity of meta * int
exception MetaTypeMismatch of meta * meta_arg_type * meta_arg_type
