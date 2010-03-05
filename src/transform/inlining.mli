(* Inline the definition not recursive *)

val t : Transform.t


(* Function to use in other transformations if inlining is needed *)

type env

val empty_env : env

(*val add_decl : env -> Theory.decl -> env *)

val replacet : env -> Term.term -> Term.term 
val replacep : env -> Term.fmla -> Term.fmla
