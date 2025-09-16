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

Definition acc {a:Type} (r:a -> a -> bool) : a -> Prop :=
  Acc (fun y x => r y x = true).

Definition well_founded {a:Type} (r:a -> a -> bool) : Prop :=
  well_founded (fun y x => r y x = true).
