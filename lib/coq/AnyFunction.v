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

Require Import BuiltIn.
Require Import HighOrd.

Definition any_function: forall {a:Type} {a_WT:WhyType a}
  {b:Type} {b_WT:WhyType b}, a -> b.
intros A _ B (b,_) _.
exact b.
Defined.
