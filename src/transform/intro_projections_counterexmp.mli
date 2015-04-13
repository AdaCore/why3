(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val intro_projections_counterexmp :  Task.task Trans.trans
 (** [intros G f] returns the declarations after introducing
     new constant symbol for every term with model label that has the
     same type as an argument of some function labeled with meta
     model_projection in the goal [goal G : f] *)
