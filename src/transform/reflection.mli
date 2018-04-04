val reflection_by_lemma: Decl.prsymbol -> Env.env -> Task.task Trans.tlist

val reflection_by_function: bool -> string -> Env.env -> Task.task Trans.tlist
