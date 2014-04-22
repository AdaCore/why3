open Why3
open Term

type reason =
   | VC_Division_Check
   | VC_Index_Check
   | VC_Overflow_Check
   | VC_Range_Check
   | VC_Length_Check
   | VC_Discriminant_Check
   | VC_Initial_Condition
   | VC_Precondition
   | VC_Precondition_Main
   | VC_Postcondition
   | VC_Refined_Post
   | VC_Contract_Case
   | VC_Disjoint_Contract_Cases
   | VC_Complete_Contract_Cases
   | VC_Loop_Invariant
   | VC_Loop_Invariant_Init
   | VC_Loop_Invariant_Preserv
   | VC_Loop_Variant
   | VC_Assert
   | VC_Raise

type subp_entity = Gnat_loc.loc

type id = int
type check = { id : id ; reason : reason; sloc : Gnat_loc.loc }
let check_compare a b =
  let c = Pervasives.compare a.id b.id in
  if c <> 0 then c
  else Pervasives.compare a.reason b.reason

let check_equal a b =
  Pervasives.(=) a.id b.id && Pervasives.(=) a.reason b.reason

let check_hash e = Hashcons.combine (Hashtbl.hash e.id) (Hashtbl.hash e.reason)

let mk_check reason id sloc =
  { reason = reason; id = id ; sloc = sloc }

let get_loc c = c.sloc
let get_reason c = c.reason
let reason_from_string s =
   match s with
   | "VC_DIVISION_CHECK"          -> VC_Division_Check
   | "VC_INDEX_CHECK"             -> VC_Index_Check
   | "VC_OVERFLOW_CHECK"          -> VC_Overflow_Check
   | "VC_RANGE_CHECK"             -> VC_Range_Check
   | "VC_LENGTH_CHECK"            -> VC_Length_Check
   | "VC_DISCRIMINANT_CHECK"      -> VC_Discriminant_Check
   | "VC_INITIAL_CONDITION"       -> VC_Initial_Condition
   | "VC_PRECONDITION"            -> VC_Precondition
   | "VC_PRECONDITION_MAIN"       -> VC_Precondition_Main
   | "VC_POSTCONDITION"           -> VC_Postcondition
   | "VC_REFINED_POST"            -> VC_Refined_Post
   | "VC_CONTRACT_CASE"           -> VC_Contract_Case
   | "VC_DISJOINT_CONTRACT_CASES" -> VC_Disjoint_Contract_Cases
   | "VC_COMPLETE_CONTRACT_CASES" -> VC_Complete_Contract_Cases
   | "VC_LOOP_INVARIANT"          -> VC_Loop_Invariant
   | "VC_LOOP_INVARIANT_INIT"     -> VC_Loop_Invariant_Init
   | "VC_LOOP_INVARIANT_PRESERV"  -> VC_Loop_Invariant_Preserv
   | "VC_LOOP_VARIANT"            -> VC_Loop_Variant
   | "VC_ASSERT"                  -> VC_Assert
   | "VC_RAISE"                   -> VC_Raise
   | _                            ->
       Format.printf "unknown VC reason: %s@." s;
       Gnat_util.abort_with_message ""

let reason_to_ada reason =
   match reason with
   | VC_Division_Check          -> "VC_DIVISION_CHECK"
   | VC_Index_Check             -> "VC_INDEX_CHECK"
   | VC_Overflow_Check          -> "VC_OVERFLOW_CHECK"
   | VC_Range_Check             -> "VC_RANGE_CHECK"
   | VC_Length_Check            -> "VC_LENGTH_CHECK"
   | VC_Discriminant_Check      -> "VC_DISCRIMINANT_CHECK"
   | VC_Initial_Condition       -> "VC_INITIAL_CONDITION"
   | VC_Precondition            -> "VC_PRECONDITION"
   | VC_Precondition_Main       -> "VC_PRECONDITION_MAIN"
   | VC_Postcondition           -> "VC_POSTCONDITION"
   | VC_Refined_Post            -> "VC_REFINED_POST"
   | VC_Contract_Case           -> "VC_CONTRACT_CASE"
   | VC_Disjoint_Contract_Cases -> "VC_DISJOINT_CONTRACT_CASES"
   | VC_Complete_Contract_Cases -> "VC_COMPLETE_CONTRACT_CASES"
   | VC_Loop_Invariant          -> "VC_LOOP_INVARIANT"
   | VC_Loop_Invariant_Init     -> "VC_LOOP_INVARIANT_INIT"
   | VC_Loop_Invariant_Preserv  -> "VC_LOOP_INVARIANT_PRESERV"
   | VC_Loop_Variant            -> "VC_LOOP_VARIANT"
   | VC_Assert                  -> "VC_ASSERT"
   | VC_Raise                   -> "VC_RAISE"

type gp_label =
  | Gp_Sloc of Gnat_loc.loc
  | Gp_Subp of Gnat_loc.loc
  | Gp_VC_Id of int
  | Gp_Reason of reason
  | Gp_Pretty_Ada of int

let read_label s =
    if Strings.starts_with s "GP_" then
       match Gnat_util.colon_split s with
       | ["GP_Reason"; reason] ->
             Some (Gp_Reason (reason_from_string reason))
       | ["GP_Pretty_Ada"; msg] ->
           begin try
             Some (Gp_Pretty_Ada (int_of_string msg))
           with Failure _ ->
              Format.printf "GP_Pretty_Ada: cannot parse string: %s" s;
              Gnat_util.abort_with_message ""
           end
       | ["GP_Id"; msg] ->
           begin try
             Some (Gp_VC_Id (int_of_string msg))
           with Failure _ ->
              Format.printf "GP_VC_Id: cannot parse string: %s" s;
              Gnat_util.abort_with_message ""
           end
       | "GP_Sloc" :: rest ->
           begin try Some (Gp_Sloc (Gnat_loc.parse_loc rest))
           with Failure _ ->
              Format.printf "GP_Sloc: cannot parse string: %s" s;
              Gnat_util.abort_with_message ""
           end
       | ["GP_Subp" ; file ; line ] ->
           begin try
             Some (Gp_Subp (Gnat_loc.mk_loc_line file (int_of_string line)))
           with Failure _ ->
              Format.printf "GP_Subp: cannot parse string: %s" s;
              Gnat_util.abort_with_message ""
           end
       | _ ->
              Format.printf "cannot parse string: %s@." s;
             Gnat_util.abort_with_message
                 "found malformed GNATprove label"
    else None

type my_expl =
   { mutable check_id : int option;
     mutable check_reason : reason option;
     mutable extra_node : int option;
     mutable check_sloc : Gnat_loc.loc option
   }
(* The type that is used to extract information from a VC, is filled up field
   by field *)

let read_vc_labels s =
   (* This function takes a set of labels and extracts a "node_info" from that
      set. We start with an empty record; We fill it up by iterating over all
      labels of the node. *)
   let b = { check_id      = None;
             check_reason  = None;
             check_sloc    = None;
             extra_node    = None } in
   Ident.Slab.iter
     (fun x ->
        let s = x.Ident.lab_string in
        match read_label s with
        | Some Gp_Reason reason ->
            b.check_reason <- Some reason
        | Some Gp_VC_Id i ->
            b.check_id <- Some i
        | Some Gp_Pretty_Ada node ->
            b.extra_node <- Some node
        | Some Gp_Sloc loc ->
            b.check_sloc <- Some loc
        | Some Gp_Subp _ ->
             Gnat_util.abort_with_message
                 "read_vc_labels: GP_Subp unexpected here"
        | None ->
            ()
     ) s;
     (* We potentially need to rectify in the case of loop invariants: We need
        to check whether the VC is for initialization or preservation *)
     if b.check_reason = Some VC_Loop_Invariant then begin
        Ident.Slab.iter (fun x ->
           let s = x.Ident.lab_string in
           if Strings.starts_with s "expl:" then
              if s = "expl:loop invariant init" then
                 b.check_reason <- Some VC_Loop_Invariant_Init
              else
                 b.check_reason <- Some VC_Loop_Invariant_Preserv) s
     end;
     b

let extract_check s =
     match read_vc_labels s with
     | { check_id = Some id ;
         check_reason = Some reason;
         check_sloc = Some sloc } ->
           Some (mk_check reason id sloc)
     | _ -> None

let extract_sloc s = (read_vc_labels s).check_sloc

let rec extract_msg t =
   match t.t_node with
   | Tbinop (Timplies,_, t) -> extract_msg t
   | Tlet (_,tb) | Teps tb ->
         let _, t = t_open_bound tb in
         extract_msg t
   | Tquant (_,tq) ->
         let _,_,t = t_open_quant tq in
         extract_msg t
   | _ ->
         read_vc_labels t.t_label

let get_extra_info task =
   let info = extract_msg (Task.task_goal_fmla task) in
   info.extra_node

let to_filename unitname check =
  Format.sprintf "%s_%d_%s"
    unitname check.id (reason_to_ada check.reason)

module CheckCmp = struct
   type t = check
   let compare = check_compare
end

module MCheck = Extmap.Make(CheckCmp)
module SCheck = Extset.Make(CheckCmp)
module HCheck = Hashtbl.Make (struct
   type t = check
   let equal = check_equal

   let hash = check_hash
end)
