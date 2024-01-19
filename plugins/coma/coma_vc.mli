open Why3.Term
open Coma_syntax

type context

val c_empty : context

val vc_expr : context -> expr -> term

val vc_defn : context -> bool -> defn list -> context * (hsymbol * term) list

val vc_spec : context -> hsymbol -> vsymbol list -> param list ->
                                (Why3.Ident.preid * vsymbol list * term) list
