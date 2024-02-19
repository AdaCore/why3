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
  | Ecut of term * expr
  | Ebox of expr
  | Ewox of expr
  | Eany

and argument =
  | At of ty
  | Av of term
  | Ar of vsymbol
  | Ac of expr

and defn = hsymbol * vsymbol list * param list * expr

type formula =
  | Fsym of hsymbol
  | Fagt of formula * ty
  | Fagv of formula * term
  | Fagr of formula * vsymbol
  | Fagc of formula * formula
  | Fand of formula * formula
  | Fcut of term * bool * formula
  | Flam of param list * Shs.t * formula
  | Fall of param list * formula
  | Fneu of formula * Shs.t

val debug_slow : Debug.flag
