open Why3
open Coma_logic
open Coma_syntax

type ctx

val ctx0 : ctx

val type_prog : ?loc:Loc.position -> Theory.theory_uc -> ctx -> pexpr -> expr

val type_defn_list : Theory.theory_uc -> ctx -> bool -> pdefn list -> ctx * defn list
