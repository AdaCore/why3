(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val intro_projections_counterexmp :  Env.env -> Task.task Trans.trans
 (**
    Transformation that for each declared abstract function or predicate
    p labeled with label "model_projected" creates a declaration of new
    constant c labeled with label "model" and declaration of new axiom
    stating that c = f p where f is projection for p.

    Projections are composed from projection functions. Projection function
    is a function with a single argument tagged with metas "model_projection".
    Projection f for abstract function or predicate p is defined as:
    f = pf_n ... pf_1 id where id is identity function and pf_i for i = 1 .. n
    are projection functions for that it holds that the argument of pf_1 is of
    the same type as p, the return value of pf_i is of the same type as the argument
    of pf_i+1, for all i, j = 1 .. n pf_i <> pf_j, and there is no projection
    function pf that could further project f.
    projected.
    That is, projection for p is identify if there is no projection function with
    an argument of the same type as p.

    Projections can be given names by labeling projection function by label
    of the form "model_trace:proj_name".
    If predicate p has has a label of the form "model_trace:p_name@*",
    the constant will have a label of the form "model_trace:p_nameproj_name@*".
    This is especially usefull when projetions are projecting record type
    to its elements (there is one projection for every record element with
    name ".record_element_name".

    Note that in order this work, projection functions cannot be inlined.
    If inlining transformation is performed, projection functions must
    be marked with meta "inline : no".

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