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

(** {1 Program Declarations} *)

open Ident
open Term
open Mlw_ty
open Mlw_ty.T
open Mlw_expr


(** {2 Type declaration} *)

type constructor = plsymbol * plsymbol option list

type data_decl = itysymbol * constructor list * post

(** {2 Declaration type} *)

type pdecl = private {
  pd_node : pdecl_node;
  pd_syms : Sid.t;         (* idents used in declaration *)
  pd_news : Sid.t;         (* idents introduced in declaration *)
  pd_tag  : int;           (* unique tag *)
}

and pdecl_node = private
  | PDtype of itysymbol
  | PDdata of data_decl list
  | PDval  of let_sym
  | PDlet  of let_defn
  | PDrec  of fun_defn list
  | PDexn  of xsymbol

(** {2 Marks} *)

val ts_mark : Ty.tysymbol
val ty_mark : Ty.ty
val ity_mark : ity
val pv_old : pvsymbol

(** {2 Declaration constructors} *)

type pre_field = preid option * field

type pre_constructor = preid * pre_field list

type pre_data_decl = itysymbol * pre_constructor list

val create_data_decl : pre_data_decl list -> pdecl

val create_ty_decl : itysymbol -> pdecl

val create_val_decl : let_sym -> pdecl

val create_let_decl : let_defn -> pdecl

val create_rec_decl : fun_defn list -> pdecl

val create_exn_decl : xsymbol -> pdecl

(** {2 Type invariants} *)

val null_invariant : itysymbol -> post

val add_invariant : pdecl -> itysymbol -> post -> pdecl

(** {2 Cloning} *)

val clone_data_decl : Mlw_expr.symbol_map -> pdecl -> pdecl

(** {2 Known identifiers} *)

type known_map = pdecl Mid.t

val known_id : known_map -> ident -> unit
val known_add_decl : Decl.known_map -> known_map -> pdecl -> known_map
val merge_known : known_map -> known_map -> known_map

val find_constructors : known_map -> itysymbol -> constructor list
val find_invariant : known_map -> itysymbol -> post
val find_definition : known_map -> psymbol -> fun_defn option

exception NonupdatableType of ity

val inst_constructors :
  Decl.known_map -> known_map -> ity -> (lsymbol * field list) list
