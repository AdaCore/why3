
open Ty
open Term
open Decl

type inline = known_map -> lsymbol -> ty list -> ty option -> bool

val eval_match: inline:inline -> known_map -> term -> term

val inline_nonrec_linear : inline

