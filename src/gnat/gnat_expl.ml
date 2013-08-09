open Why3
open Term
open Gnat_loc

type reason =
   | VC_Division_Check
   | VC_Index_Check
   | VC_Overflow_Check
   | VC_Range_Check
   | VC_Length_Check
   | VC_Discriminant_Check
   | VC_Precondition
   | VC_Postcondition
   | VC_Contract_Case
   | VC_Disjoint_Contract_Cases
   | VC_Complete_Contract_Cases
   | VC_Loop_Invariant
   | VC_Loop_Invariant_Init
   | VC_Loop_Invariant_Preserv
   | VC_Loop_Variant
   | VC_Assert

type expl = { loc : loc ; reason : reason }

let expl_compare e1 e2 =
   let c = Gnat_loc.compare e1.loc e2.loc in
   if c = 0 then Pervasives.compare e1.reason e2.reason
   else c

let expl_equal e1 e2 =
   e1.loc = e2.loc && e1.reason = e2.reason

let expl_hash e =
   Hashcons.combine (Hashtbl.hash e.loc) (Hashtbl.hash e.reason)

let mk_expl reason sloc =
   { reason = reason; loc = sloc }

let reason_from_string s =
   match s with
   | "VC_DIVISION_CHECK"          -> VC_Division_Check
   | "VC_INDEX_CHECK"             -> VC_Index_Check
   | "VC_OVERFLOW_CHECK"          -> VC_Overflow_Check
   | "VC_RANGE_CHECK"             -> VC_Range_Check
   | "VC_LENGTH_CHECK"            -> VC_Length_Check
   | "VC_DISCRIMINANT_CHECK"      -> VC_Discriminant_Check
   | "VC_PRECONDITION"            -> VC_Precondition
   | "VC_POSTCONDITION"           -> VC_Postcondition
   | "VC_CONTRACT_CASE"           -> VC_Contract_Case
   | "VC_DISJOINT_CONTRACT_CASES" -> VC_Disjoint_Contract_Cases
   | "VC_COMPLETE_CONTRACT_CASES" -> VC_Complete_Contract_Cases
   | "VC_LOOP_INVARIANT"          -> VC_Loop_Invariant
   | "VC_LOOP_INVARIANT_INIT"     -> VC_Loop_Invariant_Init
   | "VC_LOOP_INVARIANT_PRESERV"  -> VC_Loop_Invariant_Preserv
   | "VC_LOOP_VARIANT"            -> VC_Loop_Variant
   | "VC_ASSERT"                  -> VC_Assert
   | _                            ->
       Format.printf "unknown VC reason: %s@." s;
       Gnat_util.abort_with_message ""

let string_of_reason s =
   match s with
   | VC_Division_Check            -> "division check"
   | VC_Index_Check               -> "index check"
   | VC_Overflow_Check            -> "overflow check"
   | VC_Range_Check               -> "range check"
   | VC_Length_Check              -> "length check"
   | VC_Discriminant_Check        -> "discriminant check"
   | VC_Precondition              -> "precondition"
   | VC_Postcondition             -> "postcondition"
   | VC_Contract_Case             -> "contract case"
   | VC_Disjoint_Contract_Cases   -> "disjoint contract cases"
   | VC_Complete_Contract_Cases   -> "complete contract cases"
   | VC_Loop_Invariant            -> "loop invariant"
   | VC_Loop_Invariant_Init       -> "loop invariant initialization"
   | VC_Loop_Invariant_Preserv    -> "loop invariant preservation"
   | VC_Loop_Variant              -> "loop variant"
   | VC_Assert                    -> "assertion"

let tag_of_reason s =
  match s with
   | VC_Division_Check            -> "division_check"
   | VC_Index_Check               -> "index_check"
   | VC_Overflow_Check            -> "overflow_check"
   | VC_Range_Check               -> "range_check"
   | VC_Length_Check              -> "length_check"
   | VC_Discriminant_Check        -> "discriminant_check"
   | VC_Precondition              -> "precondition"
   | VC_Postcondition             -> "postcondition"
   | VC_Contract_Case             -> "contract_case"
   | VC_Disjoint_Contract_Cases   -> "disjoint_contract_cases"
   | VC_Complete_Contract_Cases   -> "complete_contract_cases"
   | VC_Loop_Invariant            -> "loop_invariant"
   | VC_Loop_Invariant_Init       -> "loop_invariant_initialization"
   | VC_Loop_Invariant_Preserv    -> "loop_invariant_preservation"
   | VC_Loop_Variant              -> "loop_variant"
   | VC_Assert                    -> "assertion"

type gp_label =
  | Gp_Sloc of Gnat_loc.loc
  | Gp_Subp of Gnat_loc.loc
  | Gp_Sloc_VC of Gnat_loc.loc
  | Gp_Reason of reason
  | Gp_Pretty_Ada of string

let read_label s =
    if Gnat_util.starts_with s "GP_" then
       match Gnat_util.colon_split s with
       | ["GP_Reason"; reason] ->
             Some (Gp_Reason (reason_from_string reason))
       | ["GP_Pretty_Ada"; msg] ->
             Some (Gp_Pretty_Ada msg)
       | "GP_Sloc" :: rest ->
           begin try Some (Gp_Sloc (Gnat_loc.parse_loc rest))
           with Failure "int_of_string" ->
              Format.printf "GP_Sloc: cannot parse string: %s" s;
              Gnat_util.abort_with_message ""
           end
       | "GP_Sloc_VC" :: rest ->
           begin try Some (Gp_Sloc_VC (Gnat_loc.parse_loc rest))
           with Failure "int_of_string" ->
              Format.printf "GP_Sloc_VC: cannot parse string: %s" s;
              Gnat_util.abort_with_message ""
           end
       | ["GP_Subp" ; file ; line ] ->
           begin try
             Some (Gp_Subp (Gnat_loc.mk_loc_line file (int_of_string line)))
           with Failure "int_of_string" ->
              Format.printf "GP_Subp: cannot parse string: %s" s;
              Gnat_util.abort_with_message ""
           end
       | _ ->
             Gnat_util.abort_with_message
                 "found malformed GNATprove label"
    else None

let get_loc e = e.loc
let get_reason e = e.reason

let print_reason fmt r =
   Format.fprintf fmt "%s" (string_of_reason r)


type sloc_options =
   | VC_Sloc of Gnat_loc.loc
   | Reg_Sloc of Gnat_loc.loc
   | No_Sloc

type my_expl =
   { mutable expl_loc : sloc_options ;
     mutable expl_reason : reason option ;
     mutable expl_msg : string option
   }
(* The type that is used to extract information from a VC, is filled up field
   by field *)

type node_info =
   | Expl of expl
   | Sloc of Gnat_loc.loc
   | No_Info
(* The information that has been found in a node *)

let read_vc_labels s =
   let b = { expl_loc    = No_Sloc;
             expl_reason = None;
             expl_msg    = None } in
   Ident.Slab.iter
     (fun x ->
        let s = x.Ident.lab_string in
        match read_label s with
        | Some Gp_Reason reason ->
            b.expl_reason <- Some reason
        | Some Gp_Pretty_Ada msg ->
            b.expl_msg <- Some msg
        | Some Gp_Sloc loc ->
            begin
               match b.expl_loc with
               | VC_Sloc _ -> ()
               | _ -> b.expl_loc <- Reg_Sloc loc
            end
        | Some Gp_Sloc_VC loc ->
            b.expl_loc <- VC_Sloc loc
        | Some Gp_Subp _ ->
             Gnat_util.abort_with_message
                 "read_vc_labels: GP_Subp unexpected here"
        | None ->
            ()
     ) s;
     (* We potentially need to rectify in the case of loop invariants: We need
        to check whether the VC is for initialization or preservation *)
     if b.expl_reason = Some VC_Loop_Invariant then begin
        Ident.Slab.iter (fun x ->
           let s = x.Ident.lab_string in
           if Gnat_util.starts_with s "expl:" then
              if s = "expl:loop invariant init" then
                 b.expl_reason <- Some VC_Loop_Invariant_Init
              else
                 b.expl_reason <- Some VC_Loop_Invariant_Preserv) s
     end;
     b

let extract_explanation s =
   (* This function takes a set of labels and extracts a "node_info" from that
      set. We start with an empty record; We fill it up by iterating over all
      labels of the node. If the record is entirely filled, we return an
      "Expl"; if there was at least a location, we return a "Sloc";
      otherwise we return "No_Info" *)
     match read_vc_labels s with
     | { expl_loc = VC_Sloc sloc ;
         expl_reason = Some reason } ->
           Expl (mk_expl reason sloc)
     | { expl_loc = Reg_Sloc sloc ;
         expl_reason = _;
         expl_msg = None } ->
           Sloc sloc
     | _ ->
           No_Info

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

let simple_print_expl fmt p =
  match p.loc with
  | [] -> assert false
  | primary :: _ ->
      Format.fprintf fmt "%a:%a" simple_print_loc primary print_reason p.reason

let improve_sloc sloc task =
   let info = extract_msg (Task.task_goal_fmla task) in
   let sloc =
      match info.expl_loc with
      | No_Sloc -> sloc
      | VC_Sloc s | Reg_Sloc s -> List.hd s
   in
   let msg =
      match info.expl_msg with
      | None -> ""
      | Some s -> s
   in
   sloc, msg
let print_skipped fmt p =
   Format.fprintf fmt "%a: %a skipped"
     simple_print_loc (List.hd p.loc) print_reason p.reason

let to_filename ?goal expl =
   let tag = tag_of_reason expl.reason in
   let l = orig_loc expl.loc in
   let l =
      match goal with
      | None -> l
      | Some g -> let l, _ = improve_sloc l (Session.goal_task g) in l
   in
   Format.sprintf "%s_%d_%d_%s" (get_file l) (get_line l) (get_col l) tag

module ExplCmp = struct
   type t = expl
   let compare = expl_compare
end

module MExpl = Extmap.Make(ExplCmp)
module SExpl = Extset.Make(ExplCmp)
module HExpl = Hashtbl.Make (struct
   type t = expl
   let equal = expl_equal

   let hash = expl_hash
end)
