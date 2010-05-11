
open Why
open Term
open Pgm_ttree

module R : Set.S with type elt = reference

type t = private {
  reads  : R.t;
  writes : R.t;
  raises : Sls.t;
}

val empty : t



