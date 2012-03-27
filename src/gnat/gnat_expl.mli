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

val expl_from_label_info :
   Why3.Loc.position -> string -> string -> expl

val print_expl : bool -> Format.formatter -> expl -> unit

val print_skipped : Format.formatter -> expl -> unit

val to_filename : expl -> string
(* print a representation of an explanation that could serve as a filename *)

type loc

val mk_loc : string -> int -> int -> loc
val mk_loc_line : string -> int -> loc
val get_loc : expl -> loc

val equal_line : loc -> loc -> bool
(* compare two locations by file and line only, ignoring the column *)

module MExpl : Stdlib.Map.S with type key = expl
module HExpl : Hashtbl.S with type key = expl
