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
