type reason =
   | VC_Division_Check
   | VC_Index_Check
   | VC_Overflow_Check
   | VC_Range_Check
   | VC_Precondition
   | VC_Postcondition
   | VC_Loop_Invariant
   | VC_Loop_Invariant_Init
   | VC_Loop_Invariant_Preserv
   | VC_Assert

type expl

val reason_from_string : string -> reason

val print_expl : bool -> Format.formatter -> expl -> unit

val print_skipped : Format.formatter -> expl -> unit

val to_filename : expl -> string
(* print a representation of an explanation that could serve as a filename *)

type simple_loc

type loc
(* The type of locations. A location is a list of "simple" locations, and a
   simple location consists of file, line and column. *)

val mk_expl : reason -> loc -> loc -> expl

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

val get_loc : expl -> loc
val get_subp_loc : expl -> loc

val print_loc : Format.formatter -> loc -> unit

val simple_print_loc : Format.formatter -> simple_loc -> unit
(* only print the first sloc *)

val orig_loc : loc -> simple_loc
(* return the sloc of the original source *)

val equal_line : loc -> loc -> bool
(* compare two locations by file and line only, ignoring the column *)

module MExpl : Stdlib.Map.S with type key = expl
module HExpl : Hashtbl.S with type key = expl
