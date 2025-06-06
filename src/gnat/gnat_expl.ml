open Why3
open Term

type check_kind =
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
   | VC_Resource_Leak
   | VC_Resource_Leak_At_End_Of_Scope
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
   | VC_Validity_Check
   (* VC_Assert_Kind - assertions *)
   | VC_Initial_Condition
   | VC_Default_Initial_Condition
   | VC_Precondition
   | VC_Precondition_Main
   | VC_Postcondition
   | VC_Refined_Post
   | VC_Contract_Case
   | VC_Disjoint_Cases
   | VC_Complete_Cases
   | VC_Exceptional_Case
   | VC_Exit_Case
   | VC_Loop_Invariant
   | VC_Loop_Invariant_Init
   | VC_Loop_Invariant_Preserv
   | VC_Loop_Variant
   | VC_Subprogram_Variant
   | VC_Termination_Check
   | VC_Assert
   | VC_Assert_Premise
   | VC_Assert_Step
   | VC_Raise
   | VC_Unexpected_Program_Exit
   | VC_Program_Exit_Post
   | VC_Feasible_Post
   | VC_Inline_Check
   | VC_Container_Aggr_Check
   | VC_Reclamation_Check
   | VC_UC_No_Holes
   | VC_UC_Same_Size
   | VC_UC_Alignment
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | VC_Weaker_Pre
   | VC_Trivial_Weaker_Pre
   | VC_Stronger_Post
   | VC_Weaker_Classwide_Pre
   | VC_Stronger_Classwide_Post
   | VC_Weaker_Pre_Access
   | VC_Stronger_Post_Access
   (* VC_Warning_Kind - warnings *)
   | VC_Inconsistent_Pre
   | VC_Inconsistent_Post
   | VC_Inconsistent_Assume
   | VC_Unreachable_Branch
   | VC_Dead_Code

let is_warning_kind r =
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
   | VC_Resource_Leak
   | VC_Resource_Leak_At_End_Of_Scope
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
   | VC_Validity_Check
   (* VC_Assert_Kind - assertions *)
   | VC_Initial_Condition
   | VC_Default_Initial_Condition
   | VC_Precondition
   | VC_Precondition_Main
   | VC_Postcondition
   | VC_Refined_Post
   | VC_Contract_Case
   | VC_Disjoint_Cases
   | VC_Complete_Cases
   | VC_Exceptional_Case
   | VC_Exit_Case
   | VC_Loop_Invariant
   | VC_Loop_Invariant_Init
   | VC_Loop_Invariant_Preserv
   | VC_Loop_Variant
   | VC_Subprogram_Variant
   | VC_Termination_Check
   | VC_Assert
   | VC_Assert_Premise
   | VC_Assert_Step
   | VC_Raise
   | VC_Unexpected_Program_Exit
   | VC_Program_Exit_Post
   | VC_Feasible_Post
   | VC_Inline_Check
   | VC_Container_Aggr_Check
   | VC_Reclamation_Check
   | VC_UC_No_Holes
   | VC_UC_Same_Size
   | VC_UC_Alignment
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | VC_Weaker_Pre
   | VC_Trivial_Weaker_Pre
   | VC_Stronger_Post
   | VC_Weaker_Classwide_Pre
   | VC_Stronger_Classwide_Post
   | VC_Weaker_Pre_Access
   | VC_Stronger_Post_Access
     -> false
   (* VC_Warning_Kind - warnings *)
   | VC_Inconsistent_Pre
   | VC_Inconsistent_Post
   | VC_Inconsistent_Assume
   | VC_Unreachable_Branch
   | VC_Dead_Code
     -> true

type subp_entity = Gnat_loc.loc

type id = int
type check =
  { id             : id;
    check_kind     : check_kind;
    sloc           : Gnat_loc.loc;
    shape          : string;
    already_proved : bool
  }

type extra_info =
  { pretty_node : int option;
    inlined     : int option;
  }

type vc_info =
  { check      : check;
    extra_info : extra_info;
  }

type limit_mode =
  | Limit_Check of check
  | Limit_Line of Gnat_loc.loc
(* This type is used only to differenciate the two different uses of
   --limit-line: - --limit-line=file:line -> Limit_Line
                 - --limit-line=file:line:checkkind -> Limit_Check *)


let check_compare a b =
  let c = Stdlib.compare a.id b.id in
  if c <> 0 then c
  else Stdlib.compare a.check_kind b.check_kind

let check_equal a b =
  Stdlib.(=) a.id b.id && Stdlib.(=) a.check_kind b.check_kind

let check_hash e = Hashcons.combine (Hashtbl.hash e.id) (Hashtbl.hash e.check_kind)

let mk_check ?shape:shape check_kind id sloc ap =
  { check_kind = check_kind; id = id ; sloc = sloc ; already_proved = ap;
    shape = match shape with None -> "" | Some s -> s }

let get_loc c = c.sloc
let get_check_kind c = c.check_kind
let check_kind_from_string s =
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
   | "VC_RESOURCE_LEAK"             -> VC_Resource_Leak
   | "VC_RESOURCE_LEAK_AT_END_OF_SCOPE" -> VC_Resource_Leak_At_End_Of_Scope
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
   | "VC_VALIDITY_CHECK"            -> VC_Validity_Check
   (* VC_Assert_Kind - assertions *)
   | "VC_INITIAL_CONDITION"         -> VC_Initial_Condition
   | "VC_DEFAULT_INITIAL_CONDITION" -> VC_Default_Initial_Condition
   | "VC_PRECONDITION"              -> VC_Precondition
   | "VC_PRECONDITION_MAIN"         -> VC_Precondition_Main
   | "VC_POSTCONDITION"             -> VC_Postcondition
   | "VC_REFINED_POST"              -> VC_Refined_Post
   | "VC_CONTRACT_CASE"             -> VC_Contract_Case
   | "VC_DISJOINT_CASES"            -> VC_Disjoint_Cases
   | "VC_COMPLETE_CASES"            -> VC_Complete_Cases
   | "VC_EXCEPTIONAL_CASE"          -> VC_Exceptional_Case
   | "VC_EXIT_CASE"                 -> VC_Exit_Case
   | "VC_LOOP_INVARIANT"            -> VC_Loop_Invariant
   | "VC_LOOP_INVARIANT_INIT"       -> VC_Loop_Invariant_Init
   | "VC_LOOP_INVARIANT_PRESERV"    -> VC_Loop_Invariant_Preserv
   | "VC_LOOP_VARIANT"              -> VC_Loop_Variant
   | "VC_SUBPROGRAM_VARIANT"        -> VC_Subprogram_Variant
   | "VC_TERMINATION_CHECK"         -> VC_Termination_Check
   | "VC_ASSERT"                    -> VC_Assert
   | "VC_ASSERT_PREMISE"            -> VC_Assert_Premise
   | "VC_ASSERT_STEP"               -> VC_Assert_Step
   | "VC_RAISE"                     -> VC_Raise
   | "VC_UNEXPECTED_PROGRAM_EXIT"   -> VC_Unexpected_Program_Exit
   | "VC_PROGRAM_EXIT_POST"         -> VC_Program_Exit_Post
   | "VC_FEASIBLE_POST"             -> VC_Feasible_Post
   | "VC_INLINE_CHECK"              -> VC_Inline_Check
   | "VC_CONTAINER_AGGR_CHECK"      -> VC_Container_Aggr_Check
   | "VC_RECLAMATION_CHECK"         -> VC_Reclamation_Check
   | "VC_UC_NO_HOLES"               -> VC_UC_No_Holes
   | "VC_UC_SAME_SIZE"              -> VC_UC_Same_Size
   | "VC_UC_ALIGNMENT"              -> VC_UC_Alignment
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | "VC_WEAKER_PRE"                -> VC_Weaker_Pre
   | "VC_TRIVIAL_WEAKER_PRE"        -> VC_Trivial_Weaker_Pre
   | "VC_STRONGER_POST"             -> VC_Stronger_Post
   | "VC_WEAKER_CLASSWIDE_PRE"      -> VC_Weaker_Classwide_Pre
   | "VC_STRONGER_CLASSWIDE_POST"   -> VC_Stronger_Classwide_Post
   | "VC_WEAKER_PRE_ACCESS"         -> VC_Weaker_Pre_Access
   | "VC_STRONGER_POST_ACCESS"      -> VC_Stronger_Post_Access
   (* VC_Warning_Kind - warnings *)
   | "VC_INCONSISTENT_PRE"          -> VC_Inconsistent_Pre
   | "VC_INCONSISTENT_POST"         -> VC_Inconsistent_Post
   | "VC_INCONSISTENT_ASSUME"       -> VC_Inconsistent_Assume
   | "VC_UNREACHABLE_BRANCH"        -> VC_Unreachable_Branch
   | "VC_DEAD_CODE"                 -> VC_Dead_Code
   | _                              ->
       let s = Format.sprintf "unknown VC kind: %s@." s in
       Gnat_util.abort_with_message ~internal:true s

let check_kind_to_ada kind =
   match kind with
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
   | VC_Resource_Leak             -> "VC_RESOURCE_LEAK"
   | VC_Resource_Leak_At_End_Of_Scope -> "VC_RESOURCE_LEAK_AT_END_OF_SCOPE"
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
   | VC_Validity_Check            -> "VC_VALIDITY_CHECK"
   (* VC_Assert_Kind - assertions *)
   | VC_Initial_Condition         -> "VC_INITIAL_CONDITION"
   | VC_Default_Initial_Condition -> "VC_DEFAULT_INITIAL_CONDITION"
   | VC_Precondition              -> "VC_PRECONDITION"
   | VC_Precondition_Main         -> "VC_PRECONDITION_MAIN"
   | VC_Postcondition             -> "VC_POSTCONDITION"
   | VC_Refined_Post              -> "VC_REFINED_POST"
   | VC_Contract_Case             -> "VC_CONTRACT_CASE"
   | VC_Disjoint_Cases            -> "VC_DISJOINT_CASES"
   | VC_Complete_Cases            -> "VC_COMPLETE_CASES"
   | VC_Exceptional_Case          -> "VC_EXCEPTIONAL_CASE"
   | VC_Exit_Case                 -> "VC_EXIT_CASE"
   | VC_Loop_Invariant            -> "VC_LOOP_INVARIANT"
   | VC_Loop_Invariant_Init       -> "VC_LOOP_INVARIANT_INIT"
   | VC_Loop_Invariant_Preserv    -> "VC_LOOP_INVARIANT_PRESERV"
   | VC_Loop_Variant              -> "VC_LOOP_VARIANT"
   | VC_Subprogram_Variant        -> "VC_SUBPROGRAM_VARIANT"
   | VC_Termination_Check         -> "VC_TERMINATION_CHECK"
   | VC_Assert                    -> "VC_ASSERT"
   | VC_Assert_Premise            -> "VC_ASSERT_PREMISE"
   | VC_Assert_Step               -> "VC_ASSERT_STEP"
   | VC_Raise                     -> "VC_RAISE"
   | VC_Unexpected_Program_Exit   -> "VC_UNEXPECTED_PROGRAM_EXIT"
   | VC_Program_Exit_Post         -> "VC_PROGRAM_EXIT_POST"
   | VC_Feasible_Post             -> "VC_FEASIBLE_POST"
   | VC_Inline_Check              -> "VC_INLINE_CHECK"
   | VC_Container_Aggr_Check      -> "VC_CONTAINER_AGGR_CHECK"
   | VC_Reclamation_Check         -> "VC_RECLAMATION_CHECK"
   | VC_UC_No_Holes               -> "VC_UC_NO_HOLES"
   | VC_UC_Same_Size              -> "VC_UC_SAME_SIZE"
   | VC_UC_Alignment              -> "VC_UC_ALIGNMENT"
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | VC_Weaker_Pre                -> "VC_WEAKER_PRE"
   | VC_Trivial_Weaker_Pre        -> "VC_TRIVIAL_WEAKER_PRE"
   | VC_Stronger_Post             -> "VC_STRONGER_POST"
   | VC_Weaker_Classwide_Pre      -> "VC_WEAKER_CLASSWIDE_PRE"
   | VC_Stronger_Classwide_Post   -> "VC_STRONGER_CLASSWIDE_POST"
   | VC_Weaker_Pre_Access         -> "VC_WEAKER_PRE_ACCESS"
   | VC_Stronger_Post_Access      -> "VC_STRONGER_POST_ACCESS"
   (* VC_Warning_Kind - warnings *)
   | VC_Inconsistent_Pre          -> "VC_INCONSISTENT_PRE"
   | VC_Inconsistent_Post         -> "VC_INCONSISTENT_POST"
   | VC_Inconsistent_Assume       -> "VC_INCONSISTENT_ASSUME"
   | VC_Unreachable_Branch        -> "VC_UNREACHABLE_BRANCH"
   | VC_Dead_Code                 -> "VC_DEAD_CODE"

let check_kind_to_string kind =
   match kind with
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
   | VC_Resource_Leak             -> "resource_leak"
   | VC_Resource_Leak_At_End_Of_Scope -> "resource_leak_at_end_of_scope"
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
   | VC_Validity_Check            -> "validity"
   (* VC_Assert_Kind - assertions *)
   | VC_Initial_Condition         -> "initial_condition"
   | VC_Default_Initial_Condition -> "default_initial_condition"
   | VC_Precondition              -> "precondition"
   | VC_Precondition_Main         -> "main_precondition"
   | VC_Postcondition             -> "postcondition"
   | VC_Refined_Post              -> "refined_post"
   | VC_Contract_Case             -> "contract_case"
   | VC_Disjoint_Cases            -> "disjoint_cases"
   | VC_Complete_Cases            -> "complete_cases"
   | VC_Exceptional_Case          -> "exceptional_case"
   | VC_Exit_Case                 -> "exit_case"
   | VC_Loop_Invariant            -> "loop_invariant"
   | VC_Loop_Invariant_Init       -> "loop_invariant_init"
   | VC_Loop_Invariant_Preserv    -> "loop_invariant_preserv"
   | VC_Loop_Variant              -> "loop_variant"
   | VC_Subprogram_Variant        -> "subprogram_variant"
   | VC_Termination_Check         -> "termination_check"
   | VC_Assert                    -> "assert"
   | VC_Assert_Premise            -> "assert_premise"
   | VC_Assert_Step               -> "assert_step"
   | VC_Raise                     -> "raise"
   | VC_Unexpected_Program_Exit   -> "unexpected_program_exit"
   | VC_Program_Exit_Post         -> "program_exit_post"
   | VC_Feasible_Post             -> "feasible_post"
   | VC_Inline_Check              -> "inline_check"
   | VC_Container_Aggr_Check      -> "container_aggr_check"
   | VC_Reclamation_Check         -> "reclamation_check"
   | VC_UC_No_Holes               -> "uc_no_holes"
   | VC_UC_Same_Size              -> "uc_same_size"
   | VC_UC_Alignment              -> "alignment_check"
   (* VC_LSP_Kind - Liskov Substitution Principle *)
   | VC_Weaker_Pre                -> "weaker_pre"
   | VC_Trivial_Weaker_Pre        -> "trivial_weaker_pre"
   | VC_Stronger_Post             -> "stronger_post"
   | VC_Weaker_Classwide_Pre      -> "weaker_classwide_pre"
   | VC_Stronger_Classwide_Post   -> "stronger_classwide_post"
   | VC_Weaker_Pre_Access         -> "weaker_pre_access"
   | VC_Stronger_Post_Access      -> "stronger_post_access"
   (* VC_Warning_Kind - warnings *)
   | VC_Inconsistent_Pre          -> "inconsistent_pre"
   | VC_Inconsistent_Post         -> "inconsistent_post"
   | VC_Inconsistent_Assume       -> "inconsistent_assume"
   | VC_Unreachable_Branch        -> "unreachable_branch"
   | VC_Dead_Code                 -> "dead_code"

type gp_label =
  | Gp_Check of int * check_kind * Gnat_loc.loc
  | Gp_Pretty_Ada of int
  | Gp_Shape of string
  | Gp_Already_Proved
  | Gp_Inlined

let parse_check_string s l =
  match l with
  | id::check_kind_string::sloc_rest ->
    begin try
      Gp_Check (int_of_string id, check_kind_from_string check_kind_string, Gnat_loc.parse_loc sloc_rest)
    with e when Debug.test_flag Debug.stack_trace -> raise e
    | Failure _ ->
       let s =
         Format.sprintf "GP_Check: cannot parse string: %s" s in
        Gnat_util.abort_with_message ~internal:true s
    end
  | _ ->
       let s =
         Format.sprintf "GP_Check: cannot parse string: %s" s in
        Gnat_util.abort_with_message ~internal:true s

let read_label s =
    if Strings.has_prefix ~prefix:"GP_" s then
       match Gnat_util.colon_split s with
       | "GP_Check" :: rest ->
             Some (parse_check_string s rest)
       | ["GP_Pretty_Ada"; msg] ->
           begin try
             Some (Gp_Pretty_Ada (int_of_string msg))
           with e when Debug.test_flag Debug.stack_trace -> raise e
           | Failure _ ->
             let s =
               Format.sprintf "GP_Pretty_Ada: cannot parse string: %s" s in
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
       | ["GP_Inlined"] ->
          begin
            Some (Gp_Inlined)
          end
       | _ ->
          let msg = "found malformed GNATprove label, " in
          let s =
             Format.sprintf "%s, cannot parse string: %s" msg s in
           Gnat_util.abort_with_message ~internal:true s
    else None

type my_expl =
   { mutable check_id       : int option;
     mutable check_kind     : check_kind option;
     mutable extra_node     : int option;
     mutable check_sloc     : Gnat_loc.loc option;
     mutable shape          : string option;
     mutable already_proved : bool;
     mutable inline         : int option
   }
(* The type that is used to extract information from a VC, is filled up field
   by field *)

let default_expl =
   { check_id       = None;
     check_kind     = None;
     check_sloc     = None;
     extra_node     = None;
     shape          = None;
     already_proved = false;
     inline         = None;
   }

let read_vc_labels acc s =
   (* This function takes a set of labels and extracts a "node_info" from that
      set. We start with an empty record; We fill it up by iterating over all
      labels of the node. *)
     let b = acc in
     Ident.Sattr.iter
     (fun x ->
        let s = x.Ident.attr_string in
        match read_label s with
        | Some Gp_Check (id, kind, sloc) ->
            b.check_kind <- Some kind;
            b.check_id <- Some id;
            b.check_sloc <- Some sloc;
        | Some Gp_Pretty_Ada node ->
            b.extra_node <- Some node
        | Some Gp_Shape shape ->
           b.shape <- Some shape
        | Some Gp_Already_Proved ->
           b.already_proved <- true
        | Some Gp_Inlined ->
          if b.inline <> None then ()
          else if b.extra_node = None then b.inline <- Some (-1)
          else b.inline <- b.extra_node
        | None ->
            ()
     ) s;
     (* We potentially need to rectify in the case of loop invariants: We need
        to check whether the VC is for initialization or preservation *)
     if b.check_kind = Some VC_Loop_Invariant then begin
        Ident.Sattr.iter (fun x ->
           let s = x.Ident.attr_string in
           if Strings.has_prefix ~prefix:"expl:" s then
              if s = "expl:loop invariant init" then
                 b.check_kind <- Some VC_Loop_Invariant_Init
              else
                 b.check_kind <- Some VC_Loop_Invariant_Preserv) s
     end;
     b

(* Transform an object of my_expl type into a check *)
let extract_check b =
     match b with
     | { check_id = Some id ;
         check_kind = Some check_kind;
         check_sloc = Some sloc;
         shape = shape;
         already_proved = ap; } ->
           Some (mk_check ?shape check_kind id sloc ap)
     | _ -> None

(* Copied from Termcode and modified to use an accumulator. Traverse the
   "right" side of the term and call the callback on the attributes. We stop
   when we can't descend further in the term. *)
let search_attrs callback acc =
  let rec aux acc f =
    if f.t_ty <> None then acc
    else if Ident.Sattr.mem Term.stop_split f.Term.t_attrs then acc
    else
      let acc = callback acc f.Term.t_attrs in
      match f.t_node with
        | Term.Ttrue | Term.Tfalse | Term.Tapp _ -> acc
        | Term.Tbinop (Term.Timplies, _, f) -> aux acc f
        | Term.Tlet _ | Term.Tcase _ | Term.Tquant (Term.Tforall, _) ->
          Term.t_fold aux acc f
        | _ -> acc
  in
  aux acc

(* Search the labels in the tree and extract the vc_info. Return None if not
   enough info was found. *)
let search_labels t =
  (* need to copy default_expl here to use our own object *)
  let b = search_attrs read_vc_labels ({default_expl with check_id = None}) t in
  match extract_check b with
  | None -> None
  | Some c ->
    Some { check      = c;
           extra_info = { pretty_node = b.extra_node; inlined = b.inline }
         }

let to_filename fmt check =
  List.iter (fun x ->
      let file, line, col = Gnat_loc.explode x in
      Format.fprintf fmt "%s_%d_%d_" file line col;
  ) check.sloc;
  Format.fprintf fmt "%s" (check_kind_to_string check.check_kind)

let parse_line_spec s =
   try
     let args = Re.Str.split (Re.Str.regexp_string ":") s in
     match args with
     | [] ->
        Gnat_util.abort_with_message ~internal:true
        ("limit-line: incorrect line specification - missing ':'")
     | [fn;line] ->
         let line = int_of_string line in
         Limit_Line (Gnat_loc.mk_loc_line fn line)
     | [fn;line;col;check] ->
         let line = int_of_string line in
         let col = int_of_string col in
         let check = check_kind_from_string check in
         let loc = Gnat_loc.mk_loc fn line col None in
         Limit_Check (mk_check check 0 loc false)
     | _ ->
      Gnat_util.abort_with_message ~internal:true
      (
        "limit-line: incorrect line specification -\
         invalid parameter number, must be \
         2 or 4")
  with
   | e when Debug.test_flag Debug.stack_trace -> raise e
   | Failure "int_of_string" ->
      Gnat_util.abort_with_message ~internal:true
      ("limit-line: incorrect line specification -\
        line or column field isn't a number")

let parse_region_spec s =
   try
     let args = Re.Str.split (Re.Str.regexp_string ":") s in
     match args with
     | [] ->
        Gnat_util.abort_with_message ~internal:true
        ("limit-region: incorrect region specification - missing ':'")
     | [fn;l_start;l_end] ->
         let l_start = int_of_string l_start in
         let l_end = int_of_string l_end in
         Gnat_loc.mk_region fn l_start l_end
     | _ ->
      Gnat_util.abort_with_message ~internal:true
      (
        "limit-region: incorrect line specification -\
         invalid parameter number, must be \
         3")
  with
   | e when Debug.test_flag Debug.stack_trace -> raise e
   | Failure "int_of_string" ->
      Gnat_util.abort_with_message ~internal:true
      ("limit-region: incorrect line specification -\
        first or last line field isn't a number")


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
