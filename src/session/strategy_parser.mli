
open Why3

exception SyntaxError of string

val parse : 'a Session.env_session -> string -> Strategy.t

