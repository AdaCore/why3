open Why3
open Gnat_loc

(* If you change this type, chances are you also need to change the file
   vc_kinds.ads, and the SPARK UG *)

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

type check = { loc : loc ; reason : reason }

type subp_entity =
  { subp_name : string;
    subp_loc  : loc
  }

(* the type of labels that are used by gnatprove and recognized by gnatwhy3 *)
type gp_label =
  | Gp_Sloc of Gnat_loc.loc
  (* generic location label "GP_Sloc" *)
  | Gp_Subp of Gnat_loc.loc
  (* label "GP_Subp" used to indicate the location of the subprogram *)
  | Gp_Sloc_VC of Gnat_loc.loc
  (* label "GP_Subp" used to indicate the location of a VC *)
  | Gp_Reason of reason
  (* label "GP_Reason" used to indicate the kind of a VC *)
  | Gp_Pretty_Ada of string
  (* label "GP_Pretty_Ada" used to give the Ada source text for some
     predicate *)

val read_label : string -> gp_label option
(* parse a string into a gp_label; abort if the label starts with "GP_" but
   is not one of the predefined labels. Return [None] if the string does not
   start with "GP_" *)

type expl

val expl_compare : expl -> expl -> int

val reason_from_string : string -> reason
val print_reason : proved:bool -> Format.formatter -> reason -> unit
val tag_of_reason : reason -> string

val simple_print_expl : Format.formatter -> expl -> unit
(* simple text to represent VC, used for debugging *)

val print_skipped : Format.formatter -> expl -> unit

val to_filename : ?goal:'a Session.goal -> expl -> string
(* print a representation of an explanation that could serve as a filename *)

val mk_check : reason -> loc -> check

val check_equal : check -> check -> bool

val mk_expl : reason -> loc -> subp_entity -> expl
(* [mk_expl reason l1 se]
     reason - the kind of check for this VC
     l1     - the Ada location of the VC
     se     - the entity information for the subprogram to which the VC belongs
*)

val mk_expl_check : check -> subp_entity -> expl

val get_loc : expl -> loc
val get_reason : expl -> reason
val get_subp_entity : expl -> subp_entity

module MExpl : Extmap.S with type key = expl
module HExpl : Hashtbl.S with type key = expl

type node_info =
   | Expl of check
   | Sloc of Gnat_loc.loc
   | No_Info

val extract_explanation : Ident.Slab.t -> node_info
(* from a label set, extract the auxiliary information it contains *)

val improve_sloc :
  Gnat_loc.simple_loc -> Task.task -> Gnat_loc.simple_loc * string
