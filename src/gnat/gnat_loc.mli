type context
type simple_loc
type region

type loc = simple_loc list
(* The type of locations. A location is a list of "simple" locations, and a
   simple location consists of file, line and column. *)

val get_file : simple_loc -> string
val get_line : simple_loc -> int
val get_col : simple_loc -> int
val explode : simple_loc -> string * int * int

val mk_loc : string -> int -> int -> context option -> loc
(* construct a location that consists of a single simple location with given
   file, line and column, and an optional context *)
val mk_loc_line : string -> int -> loc
(* construct a location that consists of a single simple location with given
   file and line, column is set to 0 *)
val mk_region : string -> int -> int -> region
(* construct a region with given file and first and last line *)

val parse_loc : string list -> loc
(* parse a string list of the form:
   [file1;line1;col1;file2;col2;line2;...]
   into a location.
*)

val print_loc : Format.formatter -> loc -> unit
val print_line_loc : Format.formatter -> simple_loc -> unit
val print_region : Format.formatter -> region -> unit

val simple_print_loc : Format.formatter -> simple_loc -> unit
(* only print the first sloc *)

val orig_loc : loc -> simple_loc
(* return the sloc of the original source *)

val equal_line : loc -> loc -> bool
(* compare two locations by file and line only, ignoring the column *)

val in_region : region -> loc -> bool
(* check that a location is inside a region *)

val equal_orig_loc : loc -> loc -> bool
(* compare two location by their original location, including column *)

val compare_loc : loc -> loc -> int

module S : Extset.S with type M.key = loc
