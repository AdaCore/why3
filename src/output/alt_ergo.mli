
open Format
open Ident
open Term
open Theory

val print_term : formatter -> term -> unit

val print_fmla : formatter -> fmla -> unit

val print_context : Typing.env -> formatter -> context -> unit

val print_goal : Typing.env -> formatter -> ident * fmla * context -> unit
