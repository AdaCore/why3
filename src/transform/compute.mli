(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2026 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(********************************************************************)

val meta_rewrite : Theory.meta
val meta_rewrite_def : Theory.meta

val compute_in_goal : defs:bool -> branches:bool -> Env.env -> Task.task Trans.tlist
(** [compute_in_goal defs branches env] returns the transformation
    that computes in the goal. When [defs] is true, also unfolds
    the definition of symbols. When [branches] is true,
    also computes under branches of if and match.  *)

val compute_in_hypothesis :
  int option -> defs:bool -> branches:bool -> Decl.prsymbol option -> Env.env
  -> Task.task Trans.tlist
(** [compute_in_hypothesis n defs branches p env] returns the transformation
    that computes in hypothesis [p]. When [n] is some integer [i],
    performs at most [i] steps. *)

val simplify : (Term.lsymbol -> bool) -> Env.env -> Task.task Trans.trans
(** [simplify filter env] returns the transformation that computes in
    goal but only using definitions of symbols in [filter] and rewrite
    rules whose topmost left symbol is in [filter] *)
