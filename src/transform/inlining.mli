(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Inline non-recursive definitions *)

val intro_attr : Ident.attribute

val meta : Theory.meta

val get_counterexmp : Task.task -> bool
(**
   Returns true if counterexample should be get for the task.
*)


(** {2 Generic inlining} *)

val t :
  ?use_meta:bool ->
  ?in_goal:bool ->
  notls:(for_counterexample:bool -> Term.lsymbol -> bool) ->
  notdef:(Term.term -> bool) ->
  Task.task Trans.trans

(** [t ~use_meta ~in_goal ~notls ~notdef] returns a transformation
    that expands a symbol [ls] in the subsequent declarations unless [ls]
    satisfies one of the following conditions:
    - [ls] is defined via a (mutually) recursive definition;
    - [ls] is an inductive predicate or an algebraic type constructor;
    - [notls ls] returns [true];
    - [notdef] returns [true] on the definition of [ls];
    - [use_meta] is set and [ls] is tagged by "inline:no"

    Notice that [use_meta], [notls], [notdef] restrict only which
    symbols are inlined, not when.

    If [in_goal] is set, only the top-most symbols in the goal are expanded.
*)

(** {2 Registered Transformation} *)

val all : Task.task Trans.trans
(** [all] corresponds to the transformation "inline_all" *)

val goal : Task.task Trans.trans
(** [goal] corresponds to the transformation "inline_goal" *)

val trivial : Task.task Trans.trans
(** [trivial] corresponds to the transformation "inline_trivial"
    Inline only the trivial definition :
    logic c : t = a
    logic f(x : t,...) : t = g(y : t2,...) *)

(*
(** Functions to use in other transformations if inlining is needed *)

type env

val empty_env : env

val addfs : env -> Term.lsymbol -> Term.vsymbol list -> Term.term -> env
val addps : env -> Term.lsymbol -> Term.vsymbol list -> Term.term -> env
(** [addls env ls vs t] trigger the inlining of [ls] by the definition
    [t] with the free variables [vs]. The variables of [vs] must have
    the same type as the arguments of [ls] *)

val replacet : env -> Term.term -> Term.term
val replacep : env -> Term.term -> Term.term
*)
