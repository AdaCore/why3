(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Ident
open Ty
open Term

type hsymbol = private {
  hs_name : ident;
}

module Mhs : Extmap.S with type key = hsymbol
module Shs : Extset.S with module M = Mhs
module Hhs : Exthtbl.S with type key = hsymbol
module Whs : Weakhtbl.S with type key = hsymbol

val hs_compare : hsymbol -> hsymbol -> int
val hs_equal : hsymbol -> hsymbol -> bool
val hs_hash : hsymbol -> int

val create_hsymbol : preid -> hsymbol

type param =
  | Pt of tvsymbol
  | Pv of vsymbol
  | Pr of vsymbol
  | Pc of hsymbol * vsymbol list * param list

type expr =
  | Esym of hsymbol
  | Eapp of expr * argument
  | Elam of param list * expr
  | Edef of expr * bool * defn list
  | Eset of expr * (vsymbol * term) list
  | Elet of expr * (vsymbol * term * bool) list
  | Ecut of term * bool * expr
  | Ebox of expr
  | Ewox of expr
  | Eany

and argument =
  | At of ty
  | Av of term
  | Ar of vsymbol
  | Ac of expr

and defn = hsymbol * vsymbol list * param list * expr

val debug_slow : Debug.flag

type context

val c_empty : context

val c_known : context -> Decl.known_map -> context

val c_merge : context -> context -> context (* c_merge old new *)

val vc_expr : context -> expr -> term

val vc_defn : context -> bool -> defn list -> context * (hsymbol * term) list

val vc_spec : context -> hsymbol ->
                                (Why3.Ident.preid * vsymbol list * term) list
