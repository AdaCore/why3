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
    Transformation that for each declared abstract function and predicate 
    p labeled with label "model_projected" for that it exists a projection
    function f creates declaration of new constant c and axiom stating that
    c = f p

    Projection functions are functions tagged with meta "model_projection".
    Function f is projection function for abstract function and predicate p
    if f is tagged with meta "model_projection" and has a single argument
    of the same type as is the type of p.

    This transformation is needed in situations when we want to display not
    value of a variable, but value of a projection function applied to a variable.
    
    Note that since Why3 supports namespaces (different projection functions
    can have the same name) and input languages of solvers typically not,
    Why3 renames projection functions to avoid name clashes.
    This is why it is not possible to just store the name of the projection
    function in a label and than query the solver directly for the value of
    the projection.
    Also, it means that this transformation should thus be executed before 
    this renaming.
 *)
  
