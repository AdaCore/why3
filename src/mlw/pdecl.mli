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

type pdecl = private {
  pd_node : pdecl_node;
  pd_pure : Decl.decl list;
  pd_syms : Sid.t;
  pd_news : Sid.t;
  pd_tag  : int;
}

and pdecl_node = private
  | PDtype of its_defn list
  | PDlet  of let_defn
  | PDexn  of xsymbol
  | PDpure

val create_type_decl : its_defn list -> pdecl

val create_let_decl : let_defn -> pdecl

val create_exn_decl : xsymbol -> pdecl

val create_pure_decl : Decl.decl -> pdecl

(** {2 Built-in decls} *)

val pd_int : pdecl
val pd_real : pdecl
val pd_equ : pdecl
val pd_bool : pdecl
val pd_unit : pdecl
val pd_tuple : int -> pdecl
val pd_func : pdecl
val pd_pred : pdecl
val pd_func_app : pdecl

(** {2 Known identifiers} *)

type known_map = pdecl Mid.t

val known_id : known_map -> ident -> unit
val known_add_decl : known_map -> pdecl -> known_map
val merge_known : known_map -> known_map -> known_map
