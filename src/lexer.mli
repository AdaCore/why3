
type error

exception Error of error

val report : Format.formatter -> error -> unit

val parse_logic_file : Lexing.lexbuf -> Ptree.logic_file
