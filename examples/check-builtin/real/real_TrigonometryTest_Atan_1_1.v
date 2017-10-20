(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require Reals.R_sqrt.
Require Reals.Rbasic_fun.
Require Reals.Rtrigo_def.
Require Reals.Rtrigo1.
Require Reals.Ratan.
Require BuiltIn.
Require real.Real.
Require real.Abs.
Require real.Square.

Axiom Pi_interval : ((314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)%R < Reals.Rtrigo1.PI)%R /\
  (Reals.Rtrigo1.PI < (314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038197 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)%R)%R.

Axiom Cos_plus_pi : forall (x:R),
  ((Reals.Rtrigo_def.cos (x + Reals.Rtrigo1.PI)%R) = (-(Reals.Rtrigo_def.cos x))%R).

Axiom Sin_plus_pi : forall (x:R),
  ((Reals.Rtrigo_def.sin (x + Reals.Rtrigo1.PI)%R) = (-(Reals.Rtrigo_def.sin x))%R).

Axiom Cos_plus_pi2 : forall (x:R),
  ((Reals.Rtrigo_def.cos (x + ((05 / 10)%R * Reals.Rtrigo1.PI)%R)%R) = (-(Reals.Rtrigo_def.sin x))%R).

Axiom Sin_plus_pi2 : forall (x:R),
  ((Reals.Rtrigo_def.sin (x + ((05 / 10)%R * Reals.Rtrigo1.PI)%R)%R) = (Reals.Rtrigo_def.cos x)).

Axiom Cos_neg : forall (x:R),
  ((Reals.Rtrigo_def.cos (-x)%R) = (Reals.Rtrigo_def.cos x)).

Axiom Sin_neg : forall (x:R),
  ((Reals.Rtrigo_def.sin (-x)%R) = (-(Reals.Rtrigo_def.sin x))%R).

Axiom Cos_sum : forall (x:R) (y:R),
  ((Reals.Rtrigo_def.cos (x + y)%R) = (((Reals.Rtrigo_def.cos x) * (Reals.Rtrigo_def.cos y))%R - ((Reals.Rtrigo_def.sin x) * (Reals.Rtrigo_def.sin y))%R)%R).

Axiom Sin_sum : forall (x:R) (y:R),
  ((Reals.Rtrigo_def.sin (x + y)%R) = (((Reals.Rtrigo_def.sin x) * (Reals.Rtrigo_def.cos y))%R + ((Reals.Rtrigo_def.cos x) * (Reals.Rtrigo_def.sin y))%R)%R).

Axiom Tan_atan : forall (x:R),
  ((Reals.Rtrigo1.tan (Reals.Ratan.atan x)) = x).

(* Why3 goal *)
Theorem Atan_1 : ((Reals.Ratan.atan 1%R) = (Reals.Rtrigo1.PI / 4%R)%R).
apply Ratan.atan_1.
Qed.
