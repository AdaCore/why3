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
 (**
    Transformation that for each declared abstract function or predicate
    p labeled with label "model_projected" creates a declaration of new
    constant c labeled with label "model" and declaration of new axiom.
    If there exists a projection function f for p, the axiom states that
    c = f p, otherwise it states that c = p.

    Projection functions are functions tagged with metas "model_projection"
    and "inline : no" (the latter is needed just to prevent inlinng of this
    function).
    Function f is projection function for abstract function or predicate p
    if f is tagged with meta "model_projection" and has a single argument
    of the same type as is the type of p.

    This transformation is needed in situations when we want to display not
    value of a variable, but value of a projection function applied to a variable.
    This is needed, e.g., in cases when the type of a variable is abstract.

    Note that since Why3 supports namespaces (different projection functions
    can have the same name) and input languages of solvers typically not,
    Why3 renames projection functions to avoid name clashes.
    This is why it is not possible to just store the name of the projection
    function in a label and than query the solver directly for the value of
    the projection.
    Also, it means that this transformation must be executed before this renaming.
 *)

val intro_const_equal_to_term :
  term : Term.term ->
  const_label : Ident.Slab.t ->
  const_loc : Loc.position ->
  const_name : string ->
  axiom_name : string ->
  Decl.decl list
(** Creates declaration of new constant and declaration of axiom
    stating that the constant is equal to given term.

    @param term the term to which the new constant will be equal
    @param const_label the label of the constant
    @param const_loc the location of the constant
    @param const_name the name of the constant
    @param axiom_name the name of the axiom about the constant
    @return the definition of the constant and axiom about the constant
*)
