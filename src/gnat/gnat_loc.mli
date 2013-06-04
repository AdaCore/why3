type simple_loc

type loc = simple_loc list
(* The type of locations. A location is a list of "simple" locations, and a
   simple location consists of file, line and column. *)

val get_file : simple_loc -> string
val get_line : simple_loc -> int
val get_col : simple_loc -> int

val mk_loc : string -> int -> int -> loc
(* construct a location that consists of a single simple location with given
   file, line and column *)
val mk_loc_line : string -> int -> loc
(* construct a location that consists of a single simple location with given
   file and line, column is set to 0 *)

val parse_loc : string list -> loc
(* parse a string list of the form:
   [file1;line1;col1;file2;col2;line2;...]
   into a location.
*)

val print_loc : Format.formatter -> loc -> unit
val print_line_loc : Format.formatter -> simple_loc -> unit

val simple_print_loc : Format.formatter -> simple_loc -> unit
(* only print the first sloc *)

val orig_loc : loc -> simple_loc
(* return the sloc of the original source *)

val equal_line : loc -> loc -> bool
(* compare two locations by file and line only, ignoring the column *)

val compare : loc -> loc -> int

module S : Extset.S with type M.key = loc
