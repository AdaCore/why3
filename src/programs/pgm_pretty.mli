
open Format

val print_pv : formatter -> Pgm_types.T.pvsymbol -> unit

val print_expr : formatter -> Pgm_ttree.expr -> unit

val print_recfun : formatter -> Pgm_ttree.recfun -> unit
