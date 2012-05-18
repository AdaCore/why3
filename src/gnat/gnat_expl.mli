open Why3
open Gnat_loc

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

val print_expl : bool -> Task.task -> Format.formatter -> expl -> unit

val print_skipped : Format.formatter -> expl -> unit

val to_filename : expl -> string
(* print a representation of an explanation that could serve as a filename *)

val mk_expl : reason -> loc -> loc -> expl

val get_loc : expl -> loc
val get_subp_loc : expl -> loc

module MExpl : Stdlib.Map.S with type key = expl
module HExpl : Hashtbl.S with type key = expl
