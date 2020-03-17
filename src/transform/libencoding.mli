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

open Ty
open Term
open Decl

val debug : Debug.flag

(* meta to tag the protected types *)
val meta_kept : Theory.meta

(* meta to tag the custom base type *)
val meta_base : Theory.meta

(* sort symbol of (polymorphic) types *)
val ts_type : tysymbol

(* sort of (polymorphic) types *)
val ty_type : ty

(* ts_type declaration *)
val d_ts_type : decl

(* function symbol mapping ty_type^n to ty_type *)
val ls_of_ts : tysymbol -> lsymbol

(* convert a type to a term of type ty_type *)
val term_of_ty : term Mtv.t -> ty -> term

(* add type args to the signature of a polymorphic lsymbol *)
val ls_extend : lsymbol -> lsymbol

(* rewrite a closed formula modulo the given free typevars *)
val type_close : Stv.t -> (term Mtv.t -> 'a -> term) -> 'a -> term

(* rewrite a closed formula modulo its free typevars *)
val t_type_close : (term Mtv.t -> term -> term) -> term -> term

(* convert a type declaration to a lsymbol declaration *)
val lsdecl_of_ts : tysymbol -> decl

(* a pre-id for vsymbols and lsymbols that produce non-kept values *)
val id_unprotected : string -> Ident.preid
val is_protected_id : Ident.ident -> bool

(* a pre-id for lsymbols that treat their arguments as non-kept *)
val id_unprotecting : string -> Ident.preid
val is_protecting_id : Ident.ident -> bool

(* the value type is in kept and the ident is not unprotected *)
val is_protected_vs : Sty.t -> vsymbol -> bool
val is_protected_ls : Sty.t -> lsymbol -> bool

(* monomorphise wrt the base type, the set of kept types, and a symbol map *)
val d_monomorph : ty -> Sty.t -> (lsymbol -> lsymbol) -> decl -> decl list

(* replace all non-kept types with ty_base *)
val monomorphise_task : Task.task Trans.trans

(* replace type variables in a goal with fresh type constants *)
val monomorphise_goal : Task.task Trans.trans

(* close by subtype the set of types tagged by meta_kept *)
val close_kept : Task.task Trans.trans

(* reconstruct a definition of an lsymbol or make a defining axiom *)
val defn_or_axiom : lsymbol -> term -> decl list

