(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Ident
open Ty
open Term

(** Type declaration *)

type ty_def =
  | Tabstract
  | Talgebraic of lsymbol list

type ty_decl = tysymbol * ty_def

(** Logic declaration *)

type ls_defn

type logic_decl = lsymbol * ls_defn option

val make_ls_defn : lsymbol -> vsymbol list -> expr -> logic_decl
val make_fs_defn : lsymbol -> vsymbol list -> term -> logic_decl
val make_ps_defn : lsymbol -> vsymbol list -> fmla -> logic_decl

val open_ls_defn : ls_defn -> vsymbol list * expr
val open_fs_defn : ls_defn -> vsymbol list * term
val open_ps_defn : ls_defn -> vsymbol list * fmla

val ls_defn_axiom : ls_defn -> fmla

(** Inductive predicate declaration *)

type prsymbol = private {
  pr_name : ident;
}

module Spr : Set.S with type elt = prsymbol
module Mpr : Map.S with type key = prsymbol
module Hpr : Hashtbl.S with type key = prsymbol

val create_prsymbol : preid -> prsymbol

type prop = prsymbol * fmla

type ind_decl = lsymbol * prop list

(* Proposition declaration *)

type prop_kind =
  | Paxiom
  | Plemma
  | Pgoal

type prop_decl = prop_kind * prsymbol * fmla

(** Declaration type *)

type decl = private {
  d_node : decl_node;
  d_tag  : int;
}

and decl_node =
  | Dtype  of ty_decl list      (* recursive types *)
  | Dlogic of logic_decl list   (* recursive functions/predicates *)
  | Dind   of ind_decl list     (* inductive predicates *)
  | Dprop  of prop_decl         (* axiom / lemma / goal *)

module Sdecl : Set.S with type elt = decl
module Mdecl : Map.S with type key = decl
module Hdecl : Hashtbl.S with type key = decl

(** Declaration constructors *)

val create_ty_decl : ty_decl list -> decl
val create_logic_decl : logic_decl list -> decl
val create_ind_decl : ind_decl list -> decl
val create_prop_decl : prop_kind -> prsymbol -> fmla -> decl

(* separate independent groups of declarations *)

val create_ty_decls : ty_decl list -> decl list
val create_logic_decls : logic_decl list -> decl list
val create_ind_decls : ind_decl list -> decl list

(* exceptions *)

exception ConstructorExpected of lsymbol
exception IllegalTypeAlias of tysymbol
exception UnboundTypeVar of tvsymbol

exception InvalidIndDecl of lsymbol * prsymbol
exception TooSpecificIndDecl of lsymbol * prsymbol * term
exception NonPositiveIndDecl of lsymbol * prsymbol * lsymbol

exception IllegalConstructor of lsymbol
exception BadLogicDecl of ident
exception UnboundVars of Svs.t
exception ClashIdent of ident
exception EmptyDecl

(** Utilities *)

val decl_map : (term -> term) -> (fmla -> fmla) -> decl -> decl

(** Known identifiers *)

type known_map = decl Mid.t

val known_add_decl : known_map -> decl -> known_map
val merge_known : known_map -> known_map -> known_map

exception KnownIdent of ident
exception UnknownIdent of ident
exception RedeclaredIdent of ident

