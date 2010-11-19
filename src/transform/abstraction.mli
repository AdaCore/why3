



val abstraction : (Term.lsymbol -> bool) -> Task.task -> Task.task
(** [abstract keep t] applies variable abstraction of the task [t],
    that is replaces subterms or subformulas headed by a logic symbol
    f that do not satisfies [keep f] into a fresh variable.

    Notice that the numeric constants are always kept

    Example (approximate syntax):

    [abstraction (fun f -> List.mem f ["+";"-"]) "goal x*x+y*y = 1"]
    returns ["logic abs1 : int; logic abs2 : int; goal abs1+abs2 = 1"]

*)
