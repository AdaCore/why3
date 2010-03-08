val qualid_of_lstring : string list -> Ptree.qualid

val cloned_from_ts : Typing.env -> Theory.context -> 
  string list -> string -> Ty.tysymbol -> bool

val cloned_from_ls : Typing.env -> Theory.context -> 
  string list -> string -> Term.lsymbol -> bool

val cloned_from_pr : Typing.env -> Theory.context -> 
  string list -> string -> Theory.prop -> bool
