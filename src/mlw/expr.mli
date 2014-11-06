(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Term
open Ity

(** {2 Program symbols} *)

type psymbol = private {
  ps_name  : ident;
  ps_cty   : cty;
  ps_ghost : bool;
  ps_logic : ps_logic;
}

and ps_logic =
  | PLnone            (* non-pure symbol *)
  | PLvs of vsymbol   (* local let-function *)
  | PLls of lsymbol   (* top-level let-function or let-predicate *)
  | PLlemma           (* top-level or local let-lemma *)

module Mps : Extmap.S with type key = psymbol
module Sps : Extset.S with module M = Mps
module Hps : Exthtbl.S with type key = psymbol
module Wps : Weakhtbl.S with type key = psymbol

val ps_compare : psymbol -> psymbol -> int
val ps_equal : psymbol -> psymbol -> bool
val ps_hash : psymbol -> int

type ps_kind =
  | PKnone            (* non-pure symbol *)
  | PKlocal           (* local let-function *)
  | PKfunc of int     (* top-level let-function or constructor *)
  | PKpred            (* top-level let-predicate *)
  | PKlemma           (* top-level or local let-lemma *)

val create_psymbol : preid -> ?ghost:bool -> ?kind:ps_kind -> cty -> psymbol
(** If [?kind] is supplied and is not [PKnone], then [cty]
    must have no effects except for resets which are ignored.
    If [?kind] is [PKnone] or [PKlemma], external mutable reads
    are allowed, otherwise [cty.cty_freeze.isb_reg] must be empty.
    If [?kind] is [PKlocal], the type variables in [cty] are frozen
    but regions are instantiable. If [?kind] is [PKpred] the result
    type must be [ity_bool]. If [?kind] is [PKlemma] and the result
    type is not [ity_unit], an existential premise is generated. *)
