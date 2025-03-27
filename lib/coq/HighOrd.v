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

Require Import BuiltIn.

Definition func : forall (a:Type) (b:Type), Type.
Proof.
intros a b.
exact (a -> b).
Defined.

Definition infix_at: forall {a:Type} {b:Type}, (a -> b) -> a -> b.
Proof.
intros a b f x.
exact (f x).
Defined.

Definition pred (a: Type) := a -> bool.
