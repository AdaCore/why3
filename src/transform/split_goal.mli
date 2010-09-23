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

val asym_split : Ident.label

val split_pos : Term.fmla list -> Term.fmla -> Term.fmla list
(** [split_pos l f] returns a list [g1;..;gk] @ l such that
 f is logically equivalent to g1 /\ .. /\ gk *)

val split_neg : Term.fmla list -> Term.fmla -> Term.fmla list
(** [split_neg l f] returns a list [g1;..;gk] @ l such that
 f is logically equivalent to g1 \/ .. \/ gk *)

val split_goal : Task.task Trans.tlist
val split_all  : Task.task Trans.tlist

val right_split : Task.task Trans.tlist

