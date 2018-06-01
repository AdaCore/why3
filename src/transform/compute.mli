(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val meta_rewrite : Theory.meta

val meta_rewrite_def : Theory.meta

val normalize_goal_transf_all : Env.env -> Task.task Trans.tlist

val normalize_goal_transf_few : Env.env -> Task.task Trans.tlist

val normalize_hyp : int option -> Decl.prsymbol option -> Env.env
                    -> Task.task Trans.tlist

val normalize_hyp_few : int option -> Decl.prsymbol option -> Env.env
                    -> Task.task Trans.tlist
