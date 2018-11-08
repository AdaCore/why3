

val destruct: recursive:bool -> Decl.prsymbol -> Task.task Trans.tlist
(** [destruct ~recursive H]: On an axiom, destruct the head term of an
    hypothesis if it is either conjunction, disjunction or exists.
    If [recursive] is true, the term is recursively traversed which lead to more
    splitting.

    Efficiency: This is not optimized to be used on very big/deep
    disjunctions/conjunctions mixed.
*)
