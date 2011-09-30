val cmp_timestamps : string -> string -> int
(* compare the timestamps of two files; the files must exist *)

val cat : (string -> bool) -> string -> unit
(* cat a file (the string argument), but only lines for which the filter
   function returns [true] *)

val ends_with : string -> string -> bool
(* [ends_with s suffix] checks whether [s] ends with [suffix] *)

val starts_with : string -> string -> bool
(* [starts_with s suffix] checks whether [s] starts with [suffix] *)

val abort_with_message : string -> 'a

val output_buffer : Buffer.t -> string -> unit
(* output the buffer to a file with given filename *)
