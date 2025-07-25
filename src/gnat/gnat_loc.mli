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

val set_col : loc -> int -> loc
(* set column of the last simple loc in the list *)

val mk_loc : string -> int -> int -> context option -> loc
(* construct a location that consists of a single simple location with given
   file, line and column, and an optional context *)
val mk_loc_line : string -> int -> loc
(* construct a location that consists of a single simple location with given
   file and line, column is set to 0 *)
val mk_region : loc -> string -> int -> int -> region
(* construct a region with given file and first and last line; [loc] is a
   generic or instantiation context. *)

val parse_loc : string list -> loc
(* parse a string list of the form:
  [file1;line1;col1;context;file2;line2;col2;context;file3...]
   into a location.
   context is one of "inlined" or "instantiated".
*)

val parse_loc_line_only: string list -> loc
(* parse a string list of the form:
   [file1;line1;file2;line2;...]
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
(* compare two locations by file and line only, ignoring the column. A partial
   match (where one loc is longer than the other, but the common part matches)
   returns true. *)

val in_region : region -> loc -> bool
(* check that a location is inside a region *)

val equal_loc : loc -> loc -> bool
(* compare two locations by checking file,line,column for the first location,
   then file/line for the rest. Partial match returns true. *)

val compare_loc : loc -> loc -> int

module S : Extset.S with type M.key = loc
