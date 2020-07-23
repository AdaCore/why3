(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib

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

val import_namespace : namespace -> string list -> namespace

(** {2 Meta properties} *)

type meta_arg_type =
  | MTty
  | MTtysymbol
  | MTlsymbol
  | MTprsymbol
  | MTstring
  | MTint
  | MTid

type meta_arg =
  | MAty  of ty
  | MAts  of tysymbol
  | MAls  of lsymbol
  | MApr  of prsymbol
  | MAstr of string
  | MAint of int
  | MAid of ident

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
val meta_projection: meta
val meta_record: meta


(** {2 Theories} *)

type theory = private {
  th_name   : ident;          (* theory name *)
  th_path   : string list;    (* environment qualifiers *)
  th_decls  : tdecl list;     (* theory declarations *)
  th_ranges : tdecl Mts.t;    (* range type projections *)
  th_floats : tdecl Mts.t;    (* float type projections *)
  th_crcmap : Coercion.t;     (* implicit coercions *)
  th_export : namespace;      (* exported namespace *)
  th_known  : known_map;      (* known identifiers *)
  th_local  : Sid.t;          (* locally declared idents *)
  th_used   : Sid.t;          (* used theories *)
}

and tdecl = private {
  td_node : tdecl_node;
  td_tag  : int;
}

and tdecl_node =
  | Decl  of decl
  | Use   of theory
  | Clone of theory * symbol_map
  | Meta  of meta * meta_arg list

and symbol_map = {
  sm_ty : ty Mts.t;
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

type theory_uc = private {
  uc_name   : ident;
  uc_path   : string list;
  uc_decls  : tdecl list;
  uc_ranges : tdecl Mts.t;
  uc_floats : tdecl Mts.t;
  uc_crcmap : Coercion.t;
  uc_prefix : string list;
  uc_import : namespace list;
  uc_export : namespace list;
  uc_known  : known_map;
  uc_local  : Sid.t;
  uc_used   : Sid.t;
}

val create_theory : ?path:string list -> preid -> theory_uc
val close_theory  : theory_uc -> theory

val open_scope   : theory_uc -> string -> theory_uc
val close_scope  : theory_uc -> import:bool -> theory_uc
val import_scope : theory_uc -> string list -> theory_uc

val get_namespace : theory_uc -> namespace

val restore_path : ident -> string list * string * string list
(** [restore_path id] returns the triple (library path, theory,
   qualified symbol name) if the ident was ever introduced in
   a theory declaration. If the ident was declared in several
   different theories, the first association is retained.
   If [id] is a theory name, the third component is an empty list.
   Raises [Not_found] if the ident was never declared in/as a theory. *)

val restore_theory : ident -> theory

(** {2 Declaration constructors} *)

val create_decl : decl -> tdecl

val add_decl : ?warn:bool -> theory_uc -> decl -> theory_uc

val add_ty_decl : theory_uc -> tysymbol -> theory_uc
val add_data_decl : theory_uc -> data_decl list -> theory_uc
val add_param_decl : theory_uc -> lsymbol -> theory_uc
val add_logic_decl : theory_uc -> logic_decl list -> theory_uc
val add_ind_decl : theory_uc -> ind_sign -> ind_decl list -> theory_uc
val add_prop_decl : ?warn:bool -> theory_uc -> prop_kind -> prsymbol -> term -> theory_uc

val attr_w_non_conservative_extension_no : Ident.attribute

(** {2 Use} *)

val create_use : theory -> tdecl
val use_export : theory_uc -> theory -> theory_uc

(** {2 Clone} *)

type th_inst = {
  inst_ty : ty Mts.t;
  inst_ts : tysymbol Mts.t;
  inst_ls : lsymbol Mls.t;
  inst_pr : prop_kind Mpr.t;
  inst_df : prop_kind;
}

val empty_inst : th_inst

val warn_clone_not_abstract : Loc.position -> theory -> unit

val clone_theory : ('a -> tdecl -> 'a) -> 'a -> theory -> th_inst -> 'a

val clone_export : theory_uc -> theory -> th_inst -> theory_uc

val add_clone_internal : unit -> theory_uc -> theory -> symbol_map -> theory_uc

(** {2 Meta} *)

(* Adding registered meta for coercion *)
val meta_coercion: meta

val create_meta : meta -> meta_arg list -> tdecl

val add_meta : theory_uc -> meta -> meta_arg list -> theory_uc

val clone_meta : tdecl -> theory -> symbol_map -> tdecl option
(** [clone_meta td_meta th sm] produces from [td_meta]
    a new [Meta] tdecl instantiated with respect to [sm].
    Returns [None] if [td_meta] mentions proposition symbols
    that were not cloned (e.g. goals) or type symbols that
    were cloned into complex types. *)

(** {2 Base theories} *)

val builtin_theory : theory

val bool_theory : theory

val highord_theory : theory

val tuple_theory : int -> theory

val any_func_theory : theory

val tuple_theory_name : string -> int option

val add_decl_with_tuples : theory_uc -> decl -> theory_uc

(* {2 Exceptions} *)

type bad_instance =
  | BadI of ident
  | BadI_ty_vars of tysymbol (* type variable mismatch *)
  | BadI_ty_ner of tysymbol (* non-empty record -> ty *)
  | BadI_ty_impure of tysymbol (* impure type -> ty *)
  | BadI_ty_arity of tysymbol (* tysymbol arity mismatch *)
  | BadI_ty_rec of tysymbol (* instance with a rectype *)
  | BadI_ty_mut_lhs of tysymbol (* incompatible mutability *)
  | BadI_ty_mut_rhs of tysymbol (* incompatible mutability *)
  | BadI_ty_alias of tysymbol (* added aliased fields *)
  | BadI_field of tysymbol * vsymbol (* field not found *)
  | BadI_field_type of tysymbol * vsymbol (* incompatible field type *)
  | BadI_field_ghost of tysymbol * vsymbol (* incompatible ghost status *)
  | BadI_field_mut of tysymbol * vsymbol (* incompatible mutability *)
  | BadI_field_inv of tysymbol * vsymbol (* strengthened invariant *)
  | BadI_ls_type of lsymbol (* lsymbol type mismatch *)
  | BadI_ls_kind of lsymbol (* function/predicate mismatch *)
  | BadI_ls_arity of lsymbol (* lsymbol arity mismatch *)
  | BadI_ls_rs of lsymbol (* "val function" -> "function" *)
  | BadI_rs_arity of ident (* incompatible rsymbol arity *)
  | BadI_rs_type of ident * exn (* rsymbol type mismatch *)
  | BadI_rs_kind of ident (* incompatible rsymbol kind *)
  | BadI_rs_ghost of ident (* incompatible ghost status *)
  | BadI_rs_mask of ident (* incompatible result mask *)
  | BadI_rs_reads of ident * Svs.t (* incompatible dependencies *)
  | BadI_rs_writes of ident * Svs.t (* incompatible write effect *)
  | BadI_rs_taints of ident * Svs.t (* incompatible ghost writes *)
  | BadI_rs_covers of ident * Svs.t (* incompatible written regions *)
  | BadI_rs_resets of ident * Svs.t (* incompatible reset regions *)
  | BadI_rs_raises of ident * Sid.t (* incompatible exception set *)
  | BadI_rs_spoils of ident * Stv.t (* incompatible spoiled tyvars *)
  | BadI_rs_oneway of ident (* incompatible partiality status *)
  | BadI_xs_type of ident (* xsymbol type mismatch *)
  | BadI_xs_mask of ident (* incompatible exception mask *)

exception NonLocal of ident
exception BadInstance of bad_instance
exception CannotInstantiate of ident

exception CloseTheory
exception NoOpenedNamespace
exception ClashSymbol of string

exception KnownMeta of meta
exception UnknownMeta of string
exception BadMetaArity of meta * int
exception MetaTypeMismatch of meta * meta_arg_type * meta_arg_type

exception RangeConflict of tysymbol
exception FloatConflict of tysymbol
