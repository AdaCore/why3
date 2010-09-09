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

(** Move the conjunctions to top level and split the axiom or goal *)


val split_pos_goal      : Task.task Trans.tlist
val split_pos_neg_goal  : Task.task Trans.tlist
val split_pos_axiom     : Task.task Trans.tlist
val split_pos_neg_axiom : Task.task Trans.tlist
val split_pos_all       : Task.task Trans.tlist
val split_pos_neg_all   : Task.task Trans.tlist

(**  naming convention :
     - pos : move the conjuctions in positive sub-formula to top level
     - neg : move the conjuctions in negative sub-formula to top level
     - goal : apply the transformation only to goal
     - axiom : apply the transformation only to axioms
     - all : apply the transformation to goal and axioms *)
