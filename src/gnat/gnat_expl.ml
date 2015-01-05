open Why3
open Term

type reason =
   (* VC_RTE_Kind - run-time checks *)
   | VC_Division_Check
   | VC_Index_Check
   | VC_Overflow_Check
   | VC_Range_Check
   | VC_Length_Check
   | VC_Discriminant_Check
   | VC_Tag_Check
   (* VC_Assert_Kind - assertions *)
   | VC_Initial_Condition
   | VC_Default_Initial_Condition
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
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | VC_Weaker_Pre
   | VC_Trivial_Weaker_Pre
   | VC_Stronger_Post
   | VC_Weaker_Classwide_Pre
   | VC_Stronger_Classwide_Post

type subp_entity = Gnat_loc.loc

type id = int
type check = { id : id; reason : reason; sloc : Gnat_loc.loc; shape : string }

let check_compare a b =
  let c = Pervasives.compare a.id b.id in
  if c <> 0 then c
  else Pervasives.compare a.reason b.reason

let check_equal a b =
  Pervasives.(=) a.id b.id && Pervasives.(=) a.reason b.reason

let check_hash e = Hashcons.combine (Hashtbl.hash e.id) (Hashtbl.hash e.reason)

let mk_check ?shape:shape reason id sloc =
  { reason = reason; id = id ; sloc = sloc ;
    shape = match shape with None -> "" | Some s -> s }

let get_loc c = c.sloc
let get_reason c = c.reason
let reason_from_string s =
   match s with
   (* VC_RTE_Kind - run-time checks *)
   | "VC_DIVISION_CHECK"            -> VC_Division_Check
   | "VC_INDEX_CHECK"               -> VC_Index_Check
   | "VC_OVERFLOW_CHECK"            -> VC_Overflow_Check
   | "VC_RANGE_CHECK"               -> VC_Range_Check
   | "VC_LENGTH_CHECK"              -> VC_Length_Check
   | "VC_DISCRIMINANT_CHECK"        -> VC_Discriminant_Check
   | "VC_TAG_CHECK"                 -> VC_Tag_Check
   (* VC_Assert_Kind - assertions *)
   | "VC_INITIAL_CONDITION"         -> VC_Initial_Condition
   | "VC_DEFAULT_INITIAL_CONDITION" -> VC_Default_Initial_Condition
   | "VC_PRECONDITION"              -> VC_Precondition
   | "VC_PRECONDITION_MAIN"         -> VC_Precondition_Main
   | "VC_POSTCONDITION"             -> VC_Postcondition
   | "VC_REFINED_POST"              -> VC_Refined_Post
   | "VC_CONTRACT_CASE"             -> VC_Contract_Case
   | "VC_DISJOINT_CONTRACT_CASES"   -> VC_Disjoint_Contract_Cases
   | "VC_COMPLETE_CONTRACT_CASES"   -> VC_Complete_Contract_Cases
   | "VC_LOOP_INVARIANT"            -> VC_Loop_Invariant
   | "VC_LOOP_INVARIANT_INIT"       -> VC_Loop_Invariant_Init
   | "VC_LOOP_INVARIANT_PRESERV"    -> VC_Loop_Invariant_Preserv
   | "VC_LOOP_VARIANT"              -> VC_Loop_Variant
   | "VC_ASSERT"                    -> VC_Assert
   | "VC_RAISE"                     -> VC_Raise
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | "VC_WEAKER_PRE"                -> VC_Weaker_Pre
   | "VC_TRIVIAL_WEAKER_PRE"        -> VC_Trivial_Weaker_Pre
   | "VC_STRONGER_POST"             -> VC_Stronger_Post
   | "VC_WEAKER_CLASSWIDE_PRE"      -> VC_Weaker_Classwide_Pre
   | "VC_STRONGER_CLASSWIDE_POST"   -> VC_Stronger_Classwide_Post
   | _                            ->
       let s = Format.sprintf "unknown VC reason: %s@." s in
       Gnat_util.abort_with_message ~internal:true s

let reason_to_ada reason =
   match reason with
   (* VC_RTE_Kind - run-time checks *)
   | VC_Division_Check            -> "VC_DIVISION_CHECK"
   | VC_Index_Check               -> "VC_INDEX_CHECK"
   | VC_Overflow_Check            -> "VC_OVERFLOW_CHECK"
   | VC_Range_Check               -> "VC_RANGE_CHECK"
   | VC_Length_Check              -> "VC_LENGTH_CHECK"
   | VC_Discriminant_Check        -> "VC_DISCRIMINANT_CHECK"
   | VC_Tag_Check                 -> "VC_TAG_CHECK"
   (* VC_Assert_Kind - assertions *)
   | VC_Initial_Condition         -> "VC_INITIAL_CONDITION"
   | VC_Default_Initial_Condition -> "VC_DEFAULT_INITIAL_CONDITION"
   | VC_Precondition              -> "VC_PRECONDITION"
   | VC_Precondition_Main         -> "VC_PRECONDITION_MAIN"
   | VC_Postcondition             -> "VC_POSTCONDITION"
   | VC_Refined_Post              -> "VC_REFINED_POST"
   | VC_Contract_Case             -> "VC_CONTRACT_CASE"
   | VC_Disjoint_Contract_Cases   -> "VC_DISJOINT_CONTRACT_CASES"
   | VC_Complete_Contract_Cases   -> "VC_COMPLETE_CONTRACT_CASES"
   | VC_Loop_Invariant            -> "VC_LOOP_INVARIANT"
   | VC_Loop_Invariant_Init       -> "VC_LOOP_INVARIANT_INIT"
   | VC_Loop_Invariant_Preserv    -> "VC_LOOP_INVARIANT_PRESERV"
   | VC_Loop_Variant              -> "VC_LOOP_VARIANT"
   | VC_Assert                    -> "VC_ASSERT"
   | VC_Raise                     -> "VC_RAISE"
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | VC_Weaker_Pre                -> "VC_WEAKER_PRE"
   | VC_Trivial_Weaker_Pre        -> "VC_TRIVIAL_WEAKER_PRE"
   | VC_Stronger_Post             -> "VC_STRONGER_POST"
   | VC_Weaker_Classwide_Pre      -> "VC_WEAKER_CLASSWIDE_PRE"
   | VC_Stronger_Classwide_Post   -> "VC_STRONGER_CLASSWIDE_POST"

let reason_to_string reason =
   match reason with
   (* VC_RTE_Kind - run-time checks *)
   | VC_Division_Check            -> "division_check"
   | VC_Index_Check               -> "index_check"
   | VC_Overflow_Check            -> "overflow_check"
   | VC_Range_Check               -> "range_check"
   | VC_Length_Check              -> "length_check"
   | VC_Discriminant_Check        -> "discriminant_check"
   | VC_Tag_Check                 -> "tag_check"
   (* VC_Assert_Kind - assertions *)
   | VC_Initial_Condition         -> "initial_condition"
   | VC_Default_Initial_Condition -> "default_initial_condition"
   | VC_Precondition              -> "precondition"
   | VC_Precondition_Main         -> "main_precondition"
   | VC_Postcondition             -> "postcondition"
   | VC_Refined_Post              -> "refined_post"
   | VC_Contract_Case             -> "contract_case"
   | VC_Disjoint_Contract_Cases   -> "disjoint_contract_cases"
   | VC_Complete_Contract_Cases   -> "complete_contract_cases"
   | VC_Loop_Invariant            -> "loop_invariant"
   | VC_Loop_Invariant_Init       -> "loop_invariant_init"
   | VC_Loop_Invariant_Preserv    -> "loop_invariant_preserv"
   | VC_Loop_Variant              -> "loop_variant"
   | VC_Assert                    -> "assert"
   | VC_Raise                     -> "raise"
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | VC_Weaker_Pre                -> "weaker_pre"
   | VC_Trivial_Weaker_Pre        -> "trivial_weaker_pre"
   | VC_Stronger_Post             -> "stronger_post"
   | VC_Weaker_Classwide_Pre      -> "weaker_classwide_pre"
   | VC_Stronger_Classwide_Post   -> "stronger_classwide_post"

type gp_label =
  | Gp_Sloc of Gnat_loc.loc
  | Gp_Subp of Gnat_loc.loc
  | Gp_VC_Id of int
  | Gp_Reason of reason
  | Gp_Pretty_Ada of int
  | Gp_Shape of string

let read_label s =
    if Strings.starts_with s "GP_" then
       match Gnat_util.colon_split s with
       | ["GP_Reason"; reason] ->
             Some (Gp_Reason (reason_from_string reason))
       | ["GP_Pretty_Ada"; msg] ->
           begin try
             Some (Gp_Pretty_Ada (int_of_string msg))
           with Failure _ ->
             let s =
               Format.sprintf "GP_Pretty_Ada: cannot parse string: %s" s in
              Gnat_util.abort_with_message ~internal:true s
           end
       | ["GP_Id"; msg] ->
           begin try
             Some (Gp_VC_Id (int_of_string msg))
           with Failure _ ->
             let s = Format.sprintf "GP_VC_Id: cannot parse string: %s" s in
              Gnat_util.abort_with_message ~internal:true s
           end
       | "GP_Sloc" :: rest ->
           begin try Some (Gp_Sloc (Gnat_loc.parse_loc rest))
           with Failure _ ->
             let s = Format.sprintf "GP_Sloc: cannot parse string: %s" s in
              Gnat_util.abort_with_message ~internal:true s
           end
       | ["GP_Subp" ; file ; line ] ->
           begin try
             Some (Gp_Subp (Gnat_loc.mk_loc_line file (int_of_string line)))
           with Failure _ ->
             let s = Format.sprintf "GP_Subp: cannot parse string: %s" s in
              Gnat_util.abort_with_message ~internal:true s
           end
       | ["GP_Shape"; shape ] ->
          begin
            Some (Gp_Shape shape)
          end
       | _ ->
          let msg = "found malformed GNATprove label, " in
          let s =
             Format.sprintf "%s, cannot parse string: %s" msg s in
           Gnat_util.abort_with_message ~internal:true s
    else None

type my_expl =
   { mutable check_id : int option;
     mutable check_reason : reason option;
     mutable extra_node : int option;
     mutable check_sloc : Gnat_loc.loc option;
     mutable shape : string option
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
             extra_node    = None;
             shape         = None;
           } in
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
             Gnat_util.abort_with_message ~internal:true
                 "read_vc_labels: GP_Subp unexpected here"
        | Some Gp_Shape shape ->
           b.shape <- Some shape
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
         check_sloc = Some sloc;
         shape = shape } ->
           Some (mk_check ?shape reason id sloc)
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

let to_filename fmt check =
  List.iter (fun x ->
      let file, line, col = Gnat_loc.explode x in
      Format.fprintf fmt "%s_%d_%d_" file line col;
  ) check.sloc;
  Format.fprintf fmt "%s" (reason_to_string check.reason)

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
