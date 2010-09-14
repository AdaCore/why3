(***************************************************************

  Copyright 2010

  This module was poorly designed by Claude Marché, with the
  enormous help of Jean-Christophe Filliatre and Andrei Paskevich
  for finding the right functions in the Why3 API

**************************************************************)


(** Introduction of premises *)

(** The premises of the goal of a task are introduced in the
    context, e.g

      goal G: forall x:t, f1 -> forall y:u, f2 and f3 -> f4

    becomes

      logic x:t
      axiom H1: f1
      logic y:u
      axiom H2: f2
      axiom H3: f3
      goal G: f4

*)

val intros :  Decl.prsymbol -> Term.fmla -> Decl.decl list
 (** [intros G f] returns the declarations after introducing
     premises of [goal G : f] *)
