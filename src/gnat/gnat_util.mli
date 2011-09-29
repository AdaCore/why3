val cmp_timestamps : string -> string -> int
(* compare the timestamps of two files; the files must exist *)

val cat : (string -> bool) -> string -> unit
(* cat a file (the string argument), but only lines for which the filter
   function returns [true] *)

val ends_with : string -> string -> bool

