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


(** A reduction engine for Why3 terms *)

(*
terms are normalized with respect to

1) built-in computation rules

 a) on propositional connectives, e.g.

   f /\ true -> f

 b) on integers, e.g.

   35 + 7 -> 42

 c) on projections of pairs and of other ADTs, e.g

  fst (x,y) -> x

  cdr (Cons x y) -> y

 d) on defined function symbols, e.g.

  function sqr (x:int) = x * x

  sqr 4 -> 4 * 4 -> 16

  sqr x -> x * x

 e) (TODO?) on booleans, e.g.

  True xor False -> True

 f) (TODO?) on reals, e.g.

  1.0 + 2.5 -> 3.5

2) axioms declared as rewrite rules, thanks to the "rewrite" metas, e.g. if

    function dot : t -> t -> t
    axiom assoc: forall x y z, dot (dot x y) z = dot x (dot y z)
    meta "rewrite" assoc

  then

  dot (dot a b) (dot c d) -> dot a (dot b (dot c d))

  axioms used as rewrite rules must be either of the form

    forall ... t1 = t2

  or

    forall ... f1 <-> f2

   where the root symbol of t1 (resp. f1) is a non-interpreted function
   symbol (resp. non-interpreted predicate symbol)

  rewriting is done from left to right


*)

type engine
(** abstract type for reduction engines *)

type params = {
  compute_defs : bool;
  compute_builtin : bool;
  compute_def_set : Term.Sls.t;
}
(** Configuration of the engine.
   . [compute_defs]: if set to true, automatically compute symbols using
     known definitions. Otherwise, only symbols in [compute_def_set]
     will be computed.
   . [compute_builtin]: if set to true, compute builtin functions. *)

val create : params -> Env.env -> Decl.decl Ident.Mid.t -> engine
(** [create env known_map] creates a reduction engine with
    . builtins theories (int.Int, etc.) extracted from [env]
    . known declarations from [known_map]
    . empty set of rewrite rules
*)

exception NotARewriteRule of string

val add_rule : Term.term -> engine -> engine
(** [add_rule t e] turns [t] into a new rewrite rule and returns the
    new engine.

    raise NotARewriteRule if [t] cannot be seen as a rewrite rule
    according to the general rules given above.
*)


val normalize : ?step_limit:int -> limit:int -> engine -> Term.term -> Term.term
(** [normalize e t] normalizes the term [t] with respect to the engine
    [e]

    parameter [limit] provides a maximum number of steps for execution.
    When limit is reached, the partially reduced term is returned.
    parameter [step_limit] provides a maximum number of steps on reductions
    that would change the term even after reconstruction.
*)


open Term

exception NoMatch of (term * term * term option) option
(** [NoMatch (t1, t2, t3)] Cannot match [t1] with [t2]. If [t3] exists then [t1]
    is already matched with [t3]. *)
exception NoMatchpat of (pattern * pattern) option

type substitution = term Mvs.t

val first_order_matching: Svs.t -> term list -> term list -> Ty.ty Ty.Mtv.t * substitution
