open Why3
open Gnat_loc

type reason =
   | VC_Division_Check
   | VC_Index_Check
   | VC_Overflow_Check
   | VC_Range_Check
   | VC_Discriminant_Check
   | VC_Precondition
   | VC_Postcondition
   | VC_Loop_Invariant
   | VC_Loop_Invariant_Init
   | VC_Loop_Invariant_Preserv
   | VC_Assert

type expl

val expl_compare : expl -> expl -> int

val reason_from_string : string -> reason

val simple_print_expl : Format.formatter -> expl -> unit
(* simple text to represent VC, used for debugging *)

val print_simple_proven : Format.formatter -> expl -> unit
val print_expl : bool -> Task.task -> Format.formatter -> expl -> unit

val print_skipped : Format.formatter -> expl -> unit

val to_filename : expl -> string
(* print a representation of an explanation that could serve as a filename *)

val mk_expl : reason -> loc -> expl

val get_loc : expl -> loc

module MExpl : Stdlib.Map.S with type key = expl
module HExpl : Hashtbl.S with type key = expl

type node_info =
   | Expl of expl
   | Sloc of Gnat_loc.loc
   | No_Info

val extract_explanation : Ident.Slab.t -> node_info
(* from a label set, extract the auxiliary information it contains *)
