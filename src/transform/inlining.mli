

(* Inline the definition not recursive *)

val t :
  isnotinlinedt:(Term.term -> bool) ->
  isnotinlinedf:(Term.fmla -> bool) -> Theory.context Transform.t


(* Inline them all *)

val all : Theory.context Transform.t

(* Inline only the trivial definition :
   logic c : t = a
   logic f(x : t,...., ) : t = g(y : t2,...) *)
val trivial : Theory.context Transform.t


(* Function to use in other transformations if inlining is needed *)

type env

val empty_env : env

(*val add_decl : env -> Theory.decl -> env *)

val replacet : env -> Term.term -> Term.term 
val replacep : env -> Term.fmla -> Term.fmla
