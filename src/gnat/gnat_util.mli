val abort_with_message : internal:bool -> string -> 'a
(* print a JSON record that consists of an error message and exit.
   internal = true   - an internal error that should be reported using a bugbox
   internal = false  - a "real" error that should be reported normally
*)

val colon_split : string -> string list
(* split the given string at the character ':' *)

