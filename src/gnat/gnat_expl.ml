open Why3

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

type loc  = { file : string; line : int ; col : int }
type expl = { loc : loc ; reason : reason }

let reason_from_string s =
   match s with
   | "VC_OVERFLOW_CHECK"          -> VC_Overflow_Check
   | "VC_RANGE_CHECK"             -> VC_Range_Check
   | "VC_ARRAY_BOUNDS_CHECK"      -> VC_Array_Bounds_Check
   | "VC_DIVISION_BY_ZERO"        -> VC_Division_By_Zero
   | "VC_PRECONDITION"            -> VC_Precondition
   | "VC_POSTCONDITION"           -> VC_Postcondition
   | "VC_LOOP_INVARIANT"          -> VC_Loop_Invariant
   | "VC_LOOP_INVARIANT_INIT"     -> VC_Loop_Invariant_Init
   | "VC_LOOP_INVARIANT_PRESERV"  -> VC_Loop_Invariant_Preserv
   | "VC_ASSERT"                  -> VC_Assert
   | _                            -> assert false

let string_of_reason s =
   match s with
   | VC_Overflow_Check            -> "overflow check"
   | VC_Range_Check               -> "range check"
   | VC_Array_Bounds_Check        -> "array bounds check"
   | VC_Division_By_Zero          -> "division by zero"
   | VC_Precondition              -> "precondition"
   | VC_Postcondition             -> "postcondition"
   | VC_Loop_Invariant            -> "loop invariant"
   | VC_Loop_Invariant_Init       -> "loop invariant initialization"
   | VC_Loop_Invariant_Preserv    -> "loop invariant preservation"
   | VC_Assert                    -> "assertion"

let to_filename expl =
   let s = string_of_reason expl.reason in
   for i = 0 to String.length s - 1 do
      if s.[i] = ' ' then s.[i] <- '_'
   done;
   let l = expl.loc in
   Format.sprintf "%s_%d_%d_%s" l.file l.line l.col s

let loc_of_pos l =
   let f,l,c,_ = Loc.get l in
   { file = f; line = l; col = c }

let expl_from_label_info pos gnat_expl why_expl =
   let loc = loc_of_pos pos in
   let reason = reason_from_string gnat_expl in
   let reason =
      if reason = VC_Loop_Invariant then
         if why_expl = "loop invariant init" then
            VC_Loop_Invariant_Init
         else if why_expl = "loop invariant preservation" then
            VC_Loop_Invariant_Preserv
         else
            assert false
      else
         reason in
   { loc = loc ; reason = reason }

let print_loc fmt l =
   Format.fprintf fmt "%s:%d:%d" l.file l.line l.col

let print_reason fmt r =
   Format.fprintf fmt "%s" (string_of_reason r)

let print_expl proven fmt p =
   if proven then
      Format.fprintf fmt "%a: (info) %a proved"
        print_loc p.loc print_reason p.reason
   else
      Format.fprintf fmt "%a: %a not proved"
        print_loc p.loc print_reason p.reason

module ExplCmp = struct
   type t = expl
   let compare = Pervasives.compare
end

module MExpl = Stdlib.Map.Make(ExplCmp)
module SExpl = MExpl.Set

