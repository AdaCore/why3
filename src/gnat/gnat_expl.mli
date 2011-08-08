type reason =
   | VC_Overflow_Check
   | VC_Range_Check
   | VC_Array_Bounds_Check
   | VC_Division_By_Zero
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

module MExpl : Stdlib.Map.S with type key = expl
