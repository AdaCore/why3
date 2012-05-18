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

type expl = { loc : loc ; reason : reason ; subp : loc }
(* The subp field should not differentiate two otherwise equal explanations *)

let expl_compare e1 e2 =
   let c = Pervasives.compare e1.loc e2.loc in
   if c = 0 then Pervasives.compare e1.reason e2.reason
   else c

let expl_equal e1 e2 =
   e1.loc = e2.loc && e1.reason = e2.reason

let expl_hash e =
   Hashcons.combine (Hashtbl.hash e.loc) (Hashtbl.hash e.reason)

let mk_expl reason sloc subp_sloc =
   { reason = reason; loc = sloc; subp = subp_sloc }

let reason_from_string s =
   match s with
   | "VC_DIVISION_CHECK"          -> VC_Division_Check
   | "VC_INDEX_CHECK"             -> VC_Index_Check
   | "VC_OVERFLOW_CHECK"          -> VC_Overflow_Check
   | "VC_RANGE_CHECK"             -> VC_Range_Check
   | "VC_PRECONDITION"            -> VC_Precondition
   | "VC_POSTCONDITION"           -> VC_Postcondition
   | "VC_LOOP_INVARIANT"          -> VC_Loop_Invariant
   | "VC_LOOP_INVARIANT_INIT"     -> VC_Loop_Invariant_Init
   | "VC_LOOP_INVARIANT_PRESERV"  -> VC_Loop_Invariant_Preserv
   | "VC_ASSERT"                  -> VC_Assert
   | _                            -> assert false

let string_of_reason s =
   match s with
   | VC_Division_Check            -> "division check"
   | VC_Index_Check               -> "index check"
   | VC_Overflow_Check            -> "overflow check"
   | VC_Range_Check               -> "range check"
   | VC_Precondition              -> "precondition"
   | VC_Postcondition             -> "postcondition"
   | VC_Loop_Invariant            -> "loop invariant"
   | VC_Loop_Invariant_Init       -> "loop invariant initialization"
   | VC_Loop_Invariant_Preserv    -> "loop invariant preservation"
   | VC_Assert                    -> "assertion"

let get_loc e = e.loc
let get_subp_loc e = e.subp

let to_filename expl =
   let s = String.copy (string_of_reason expl.reason) in
   for i = 0 to String.length s - 1 do
      if s.[i] = ' ' then s.[i] <- '_'
   done;
   let l = orig_loc expl.loc in
   Format.sprintf "%s_%d_%d_%s" (get_file l) (get_line l) (get_col l) s

let print_reason fmt r =
   Format.fprintf fmt "%s" (string_of_reason r)

let print_expl proven task fmt p =
   match p.loc with
   | [] -> assert false (* the sloc of a VC is never empty *)
   | primary :: secondaries ->
         if proven then begin
            Format.fprintf fmt "%a: info: %a proved"
            simple_print_loc primary print_reason p.reason
         end else begin
            Format.fprintf fmt "%a: %a not proved"
            simple_print_loc primary print_reason p.reason;
            Format.fprintf fmt ", requires %a"
              (Driver.print_task Gnat_config.gnat_driver) task;
         end;
         List.iter
         (fun secondary_sloc ->
            Format.fprintf fmt ", in instantiation at %a"
              print_line_loc secondary_sloc) secondaries

let print_skipped fmt p =
   Format.fprintf fmt "%a: %a skipped"
     simple_print_loc (List.hd p.loc) print_reason p.reason

module ExplCmp = struct
   type t = expl
   let compare = expl_compare
end

module MExpl = Stdlib.Map.Make(ExplCmp)
module SExpl = MExpl.Set
module HExpl = Hashtbl.Make (struct
   type t = expl
   let equal = expl_equal

   let hash = expl_hash
end)
