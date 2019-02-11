open Why3

(* If you change this type, chances are you also need to change the file
   vc_kinds.ads, and the SPARK UG *)

type id = int

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

val is_warning_reason : reason -> bool
(* returns whether a VC is generated to issue possibly a warning *)

type check =
  { id             : id;
    reason         : reason;
    sloc           : Gnat_loc.loc;
    shape          : string;
    already_proved : bool
  }
(* a check is equal to a check ID as provided by gnat2why, as well as a reason.
   We need the reason because in the case of a loop invariant, there is a
   single check id, but in fact two checks (initialization and preservation).
   A check can be proved already (e.g. by CodePeer).
   *)

type subp_entity = Gnat_loc.loc

(* the type of labels that are used by gnatprove and recognized by gnatwhy3 *)
type gp_label =
  | Gp_Sloc of Gnat_loc.loc
  (* generic location label "GP_Sloc" *)
  | Gp_Subp of Gnat_loc.loc
  (* label "GP_Subp" used to indicate the location of the subprogram *)
  | Gp_VC_Id of int
  (* label "GP_VC_Id" used to indicate the id of a VC *)
  | Gp_Reason of reason
  (* label "GP_Reason" used to indicate the kind of a VC *)
  | Gp_Pretty_Ada of int
  (* label "GP_Pretty_Ada" used to give an Ada source node for some
     predicate *)
  | Gp_Shape of string
  (* label "GP_Shape" used to give a shape of the Ada code that originated
     the check *)
  | Gp_Already_Proved
  (* label "GP_Already_Proved" used to indicate that this VC doesn't require
     proof *)

val read_label : string -> gp_label option
(* parse a string into a gp_label; abort if the label starts with "GP_" but
   is not one of the predefined labels. Return [None] if the string does not
   start with "GP_" *)

val check_compare : check -> check -> int

val get_loc : check -> Gnat_loc.loc
val get_reason : check -> reason

(* Conversion functions between a reason string and the OCaml type are
   used only for debugging. The actual message tag is set by gnat2why directly.
 *)
val reason_from_string : string -> reason
(* parse a reason string from Ada into the OCaml type *)
val reason_to_ada : reason -> string
(* print a reason from the OCaml type into the Ada representation *)

val to_filename : Format.formatter -> check -> unit
(* print a representation of a check that could serve as a filename *)

val mk_check : ?shape:string -> reason -> id -> Gnat_loc.loc -> bool -> check
(* [mk_expl reason id sloc already_proved]
     reason           - the kind of check for this VC
     id               - the id of the VC
     sloc             - the sloc of the VC
     already_proved   - if the VC needs proof or not
*)

module MCheck : Extmap.S with type key = check
module HCheck : Hashtbl.S with type key = check

val extract_check : Ident.Sattr.t -> check option
(* from a label set, extract the check info, if any *)

val extract_sloc : Ident.Sattr.t -> Gnat_loc.loc option
(* from a label set, extract the sloc info it contains, if any *)

val get_extra_info : Task.task -> int option
(* from a task node, extract the Gp_Pretty_Ada info that is contained in the
 * rightmost goal node, if any *)

val search_labels: Why3.Term.term -> check option
(* Search for check labels inside a term *)
