open Why3
open Term

type reason =
   (* VC_RTE_Kind - run-time checks *)
   | VC_Division_Check
   | VC_Index_Check
   | VC_Overflow_Check
   | VC_FP_Overflow_Check
   | VC_Range_Check
   | VC_Predicate_Check
   | VC_Predicate_Check_On_Default_Value
   | VC_Null_Pointer_Dereference
   | VC_Null_Exclusion
   | VC_Invariant_Check
   | VC_Invariant_Check_On_Default_Value
   | VC_Length_Check
   | VC_Discriminant_Check
   | VC_Tag_Check
   | VC_Ceiling_Interrupt
   | VC_Interrupt_Reserved
   | VC_Ceiling_Priority_Protocol
   | VC_Task_Termination
   | VC_Initialization_Check
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
   | VC_Inline_Check
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | VC_Weaker_Pre
   | VC_Trivial_Weaker_Pre
   | VC_Stronger_Post
   | VC_Weaker_Classwide_Pre
   | VC_Stronger_Classwide_Post
   (* VC_Warning_Kind - warnings *)
   | VC_Inconsistent_Pre
   | VC_Inconsistent_Post
   | VC_Unreachable_Branch
   | VC_Dead_Code

let is_warning_reason r =
  match r with
   (* VC_RTE_Kind - run-time checks *)
   | VC_Division_Check
   | VC_Index_Check
   | VC_Overflow_Check
   | VC_FP_Overflow_Check
   | VC_Range_Check
   | VC_Predicate_Check
   | VC_Predicate_Check_On_Default_Value
   | VC_Null_Pointer_Dereference
   | VC_Null_Exclusion
   | VC_Invariant_Check
   | VC_Invariant_Check_On_Default_Value
   | VC_Length_Check
   | VC_Discriminant_Check
   | VC_Tag_Check
   | VC_Ceiling_Interrupt
   | VC_Interrupt_Reserved
   | VC_Ceiling_Priority_Protocol
   | VC_Task_Termination
   | VC_Initialization_Check
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
   | VC_Inline_Check
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | VC_Weaker_Pre
   | VC_Trivial_Weaker_Pre
   | VC_Stronger_Post
   | VC_Weaker_Classwide_Pre
   | VC_Stronger_Classwide_Post
     -> false
   (* VC_Warning_Kind - warnings *)
   | VC_Inconsistent_Pre
   | VC_Inconsistent_Post
   | VC_Unreachable_Branch
   | VC_Dead_Code
     -> true

type subp_entity = Gnat_loc.loc

type id = int
type check =
  { id             : id;
    reason         : reason;
    sloc           : Gnat_loc.loc;
    shape          : string;
    already_proved : bool
  }

let check_compare a b =
  let c = Pervasives.compare a.id b.id in
  if c <> 0 then c
  else Pervasives.compare a.reason b.reason

let check_equal a b =
  Pervasives.(=) a.id b.id && Pervasives.(=) a.reason b.reason

let check_hash e = Hashcons.combine (Hashtbl.hash e.id) (Hashtbl.hash e.reason)

let mk_check ?shape:shape reason id sloc ap =
  { reason = reason; id = id ; sloc = sloc ; already_proved = ap;
    shape = match shape with None -> "" | Some s -> s }

let get_loc c = c.sloc
let get_reason c = c.reason
let reason_from_string s =
   match s with
   (* VC_RTE_Kind - run-time checks *)
   | "VC_DIVISION_CHECK"            -> VC_Division_Check
   | "VC_INDEX_CHECK"               -> VC_Index_Check
   | "VC_OVERFLOW_CHECK"            -> VC_Overflow_Check
   | "VC_FP_OVERFLOW_CHECK"         -> VC_FP_Overflow_Check
   | "VC_RANGE_CHECK"               -> VC_Range_Check
   | "VC_PREDICATE_CHECK"           -> VC_Predicate_Check
   | "VC_PREDICATE_CHECK_ON_DEFAULT_VALUE" ->
      VC_Predicate_Check_On_Default_Value
   | "VC_NULL_POINTER_DEREFERENCE"  -> VC_Null_Pointer_Dereference 
   | "VC_NULL_EXCLUSION"            -> VC_Null_Exclusion
   | "VC_INVARIANT_CHECK"           -> VC_Invariant_Check
   | "VC_INVARIANT_CHECK_ON_DEFAULT_VALUE" ->
      VC_Invariant_Check_On_Default_Value
   | "VC_LENGTH_CHECK"              -> VC_Length_Check
   | "VC_DISCRIMINANT_CHECK"        -> VC_Discriminant_Check
   | "VC_TAG_CHECK"                 -> VC_Tag_Check
   | "VC_CEILING_INTERRUPT"         -> VC_Ceiling_Interrupt
   | "VC_INTERRUPT_RESERVED"        -> VC_Interrupt_Reserved
   | "VC_CEILING_PRIORITY_PROTOCOL" -> VC_Ceiling_Priority_Protocol
   | "VC_TASK_TERMINATION"          -> VC_Task_Termination
   | "VC_INITIALIZATION_CHECK"      -> VC_Initialization_Check
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
   | "VC_INLINE_CHECK"              -> VC_Inline_Check
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | "VC_WEAKER_PRE"                -> VC_Weaker_Pre
   | "VC_TRIVIAL_WEAKER_PRE"        -> VC_Trivial_Weaker_Pre
   | "VC_STRONGER_POST"             -> VC_Stronger_Post
   | "VC_WEAKER_CLASSWIDE_PRE"      -> VC_Weaker_Classwide_Pre
   | "VC_STRONGER_CLASSWIDE_POST"   -> VC_Stronger_Classwide_Post
   (* VC_Warning_Kind - warnings *)
   | "VC_INCONSISTENT_PRE"          -> VC_Inconsistent_Pre
   | "VC_INCONSISTENT_POST"         -> VC_Inconsistent_Post
   | "VC_UNREACHABLE_BRANCH"        -> VC_Unreachable_Branch
   | "VC_DEAD_CODE"                 -> VC_Dead_Code
   | _                              ->
       let s = Format.sprintf "unknown VC reason: %s@." s in
       Gnat_util.abort_with_message ~internal:true s

let reason_to_ada reason =
   match reason with
   (* VC_RTE_Kind - run-time checks *)
   | VC_Division_Check            -> "VC_DIVISION_CHECK"
   | VC_Index_Check               -> "VC_INDEX_CHECK"
   | VC_Overflow_Check            -> "VC_OVERFLOW_CHECK"
   | VC_FP_Overflow_Check         -> "VC_FP_OVERFLOW_CHECK"
   | VC_Range_Check               -> "VC_RANGE_CHECK"
   | VC_Predicate_Check           -> "VC_PREDICATE_CHECK"
   | VC_Predicate_Check_On_Default_Value ->
     "VC_PREDICATE_CHECK_ON_DEFAULT_VALUE"
   | VC_Null_Pointer_Dereference  -> "VC_NULL_POINTER_DEREFERENCE"
   | VC_Null_Exclusion            -> "VC_NULL_EXCLUSION"
   | VC_Invariant_Check           -> "VC_INVARIANT_CHECK"
   | VC_Invariant_Check_On_Default_Value ->
     "VC_INVARIANT_CHECK_ON_DEFAULT_VALUE"
   | VC_Length_Check              -> "VC_LENGTH_CHECK"
   | VC_Discriminant_Check        -> "VC_DISCRIMINANT_CHECK"
   | VC_Tag_Check                 -> "VC_TAG_CHECK"
   | VC_Ceiling_Interrupt         -> "VC_CEILING_INTERRUPT"
   | VC_Interrupt_Reserved        -> "VC_INTERRUPT_RESERVED"
   | VC_Ceiling_Priority_Protocol -> "VC_CEILING_PRIORITY_PROTOCOL"
   | VC_Task_Termination          -> "VC_TASK_TERMINATION"
   | VC_Initialization_Check      -> "VC_INITIALIZATION_CHECK"
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
   | VC_Inline_Check              -> "VC_INLINE_CHECK"
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | VC_Weaker_Pre                -> "VC_WEAKER_PRE"
   | VC_Trivial_Weaker_Pre        -> "VC_TRIVIAL_WEAKER_PRE"
   | VC_Stronger_Post             -> "VC_STRONGER_POST"
   | VC_Weaker_Classwide_Pre      -> "VC_WEAKER_CLASSWIDE_PRE"
   | VC_Stronger_Classwide_Post   -> "VC_STRONGER_CLASSWIDE_POST"
   (* VC_Warning_Kind - warnings *)
   | VC_Inconsistent_Pre          -> "VC_INCONSISTENT_PRE"
   | VC_Inconsistent_Post         -> "VC_INCONSISTENT_POST"
   | VC_Unreachable_Branch        -> "VC_UNREACHABLE_BRANCH"
   | VC_Dead_Code                 -> "VC_DEAD_CODE"

let reason_to_string reason =
   match reason with
   (* VC_RTE_Kind - run-time checks *)
   | VC_Division_Check            -> "division_check"
   | VC_Index_Check               -> "index_check"
   | VC_Overflow_Check            -> "overflow_check"
   | VC_FP_Overflow_Check         -> "fp_overflow_check"
   | VC_Range_Check               -> "range_check"
   | VC_Predicate_Check           -> "predicate_check"
   | VC_Predicate_Check_On_Default_Value -> "predicate_check_on_default_value"
   | VC_Null_Pointer_Dereference  -> "null_pointer_dereference"
   | VC_Null_Exclusion            -> "null_exclusion"
   | VC_Invariant_Check           -> "invariant_check"
   | VC_Invariant_Check_On_Default_Value -> "invariant_check_on_default_value"
   | VC_Length_Check              -> "length_check"
   | VC_Discriminant_Check        -> "discriminant_check"
   | VC_Tag_Check                 -> "tag_check"
   | VC_Ceiling_Interrupt         -> "ceiling_interrupt"
   | VC_Interrupt_Reserved        -> "interrupt_reserved"
   | VC_Ceiling_Priority_Protocol -> "ceiling__priority_protocol"
   | VC_Task_Termination          -> "task_termination"
   | VC_Initialization_Check      -> "initialization"
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
   | VC_Inline_Check              -> "inline_check"
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | VC_Weaker_Pre                -> "weaker_pre"
   | VC_Trivial_Weaker_Pre        -> "trivial_weaker_pre"
   | VC_Stronger_Post             -> "stronger_post"
   | VC_Weaker_Classwide_Pre      -> "weaker_classwide_pre"
   | VC_Stronger_Classwide_Post   -> "stronger_classwide_post"
   (* VC_Warning_Kind - warnings *)
   | VC_Inconsistent_Pre          -> "inconsistent_pre"
   | VC_Inconsistent_Post         -> "inconsistent_post"
   | VC_Unreachable_Branch        -> "unreachable_branch"
   | VC_Dead_Code                 -> "dead_code"

type gp_label =
  | Gp_Sloc of Gnat_loc.loc
  | Gp_Subp of Gnat_loc.loc
  | Gp_VC_Id of int
  | Gp_Reason of reason
  | Gp_Pretty_Ada of int
  | Gp_Shape of string
  | Gp_Already_Proved

let read_label s =
    if Strings.has_prefix "GP_" s then
       match Gnat_util.colon_split s with
       | ["GP_Reason"; reason] ->
             Some (Gp_Reason (reason_from_string reason))
       | ["GP_Pretty_Ada"; msg] ->
           begin try
             Some (Gp_Pretty_Ada (int_of_string msg))
           with e when Debug.test_flag Debug.stack_trace -> raise e
           | Failure _ ->
             let s =
               Format.sprintf "GP_Pretty_Ada: cannot parse string: %s" s in
              Gnat_util.abort_with_message ~internal:true s
           end
       | ["GP_Id"; msg] ->
           begin try
             Some (Gp_VC_Id (int_of_string msg))
           with e when Debug.test_flag Debug.stack_trace -> raise e
           | Failure _ ->
             let s = Format.sprintf "GP_VC_Id: cannot parse string: %s" s in
              Gnat_util.abort_with_message ~internal:true s
           end
       | "GP_Sloc" :: rest ->
           begin try Some (Gp_Sloc (Gnat_loc.parse_loc rest))
           with e when Debug.test_flag Debug.stack_trace -> raise e
           | Failure _ ->
             let s = Format.sprintf "GP_Sloc: cannot parse string: %s" s in
              Gnat_util.abort_with_message ~internal:true s
           end
       | ["GP_Subp" ; file ; line ] ->
           begin try
             Some (Gp_Subp (Gnat_loc.mk_loc_line file (int_of_string line)))
           with e when Debug.test_flag Debug.stack_trace -> raise e
           | Failure _ ->
             let s = Format.sprintf "GP_Subp: cannot parse string: %s" s in
              Gnat_util.abort_with_message ~internal:true s
           end
       | ["GP_Shape"; shape ] ->
          begin
            Some (Gp_Shape shape)
          end
       | ["GP_Already_Proved"] ->
          begin
            Some (Gp_Already_Proved)
          end
       | _ ->
          let msg = "found malformed GNATprove label, " in
          let s =
             Format.sprintf "%s, cannot parse string: %s" msg s in
           Gnat_util.abort_with_message ~internal:true s
    else None

type my_expl =
   { mutable check_id       : int option;
     mutable check_reason   : reason option;
     mutable extra_node     : int option;
     mutable check_sloc     : Gnat_loc.loc option;
     mutable shape          : string option;
     mutable already_proved : bool
   }
(* The type that is used to extract information from a VC, is filled up field
   by field *)

let read_vc_labels s =
   (* This function takes a set of labels and extracts a "node_info" from that
      set. We start with an empty record; We fill it up by iterating over all
      labels of the node. *)
   let b = { check_id       = None;
             check_reason   = None;
             check_sloc     = None;
             extra_node     = None;
             shape          = None;
             already_proved = false;
           } in
   Ident.Sattr.iter
     (fun x ->
        let s = x.Ident.attr_string in
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
        | Some Gp_Already_Proved ->
           b.already_proved <- true
        | None ->
            ()
     ) s;
     (* We potentially need to rectify in the case of loop invariants: We need
        to check whether the VC is for initialization or preservation *)
     if b.check_reason = Some VC_Loop_Invariant then begin
        Ident.Sattr.iter (fun x ->
           let s = x.Ident.attr_string in
           if Strings.has_prefix "expl:" s then
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
         shape = shape;
         already_proved = ap; } ->
           Some (mk_check ?shape reason id sloc ap)
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
         read_vc_labels t.t_attrs

let get_extra_info task =
  let f = Task.task_goal_fmla task in
  let info = extract_msg f in
  info.extra_node

let to_filename fmt check =
  List.iter (fun x ->
      let file, line, col = Gnat_loc.explode x in
      Format.fprintf fmt "%s_%d_%d_" file line col;
  ) check.sloc;
  Format.fprintf fmt "%s" (reason_to_string check.reason)

let search_labels =
  let extract_wrap l =
    match extract_check l with
    | None -> []
    | Some x -> [x] in
  let search = Termcode.search_attrs extract_wrap in
  fun f ->
    try
    begin match search f with
    | [] -> None
    | [x] -> Some x
    | _ -> assert false
    end
  with Exit -> None

module CheckCmp = struct
   type t = check
   let compare = check_compare
end

module MCheck = Extmap.Make(CheckCmp)
module HCheck = Hashtbl.Make (struct
   type t = check
   let equal = check_equal

   let hash = check_hash
end)
