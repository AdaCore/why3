(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Ty
open Term
open Ity
open Expr

(** {2 Type declarations} *)

type its_defn = private {
  itd_its          : itysymbol;
  itd_fields       : rsymbol list;
  itd_constructors : rsymbol list;
  itd_invariant    : term list;
}

val create_abstract_type_decl : preid -> tvsymbol list -> bool -> its_defn

val create_alias_decl : preid -> tvsymbol list -> ity -> its_defn

val create_flat_record_decl : preid -> tvsymbol list ->
  bool -> bool -> (bool * pvsymbol) list -> term list -> its_defn

val create_rec_record_decl : itysymbol -> pvsymbol list -> its_defn

val create_flat_variant_decl : preid -> tvsymbol list ->
  (preid * (bool * pvsymbol) list) list -> its_defn

val create_rec_variant_decl : itysymbol ->
  (preid * (bool * pvsymbol) list) list -> its_defn

(** {2 Module declarations} *)

type mdecl = private {
  md_node : mdecl_node;
  md_pure : Decl.decl list;
  md_syms : Sid.t;
  md_news : Sid.t;
  md_tag  : int;
}

and mdecl_node = private
  | MDtype of its_defn list
  | MDlet  of let_defn
  | MDexn  of xsymbol
  | MDpure

val create_type_decl : its_defn list -> mdecl

val create_let_decl : let_defn -> mdecl

val create_exn_decl : xsymbol -> mdecl

val create_pure_decl : Decl.decl -> mdecl

(** {2 Built-in decls} *)

val md_int : mdecl
val md_real : mdecl
val md_equ : mdecl
val md_bool : mdecl
val md_unit : mdecl
val md_tuple : int -> mdecl
val md_func : mdecl
val md_pred : mdecl
val md_func_app : mdecl

(** {2 Known identifiers} *)

type known_map = mdecl Mid.t

val known_id : known_map -> ident -> unit
val known_add_decl : known_map -> mdecl -> known_map
val merge_known : known_map -> known_map -> known_map
