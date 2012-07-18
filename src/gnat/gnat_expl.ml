open Why3
open Term
open Gnat_loc

type reason =
   | VC_Division_Check
   | VC_Index_Check
   | VC_Overflow_Check
   | VC_Range_Check
   | VC_Discriminant_Check
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
   | "VC_DISCRIMINANT_CHECK"      -> VC_Discriminant_Check
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
   | VC_Discriminant_Check        -> "discriminant check"
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



type my_expl =
   { mutable expl_loc : Gnat_loc.loc option ;
     mutable expl_reason : reason option ;
     mutable expl_subp : Gnat_loc.loc option;
     mutable expl_msg : string option
   }
(* The type that is used to extract information from a VC, is filled up field
   by field *)

type node_info =
   | Expl of expl
   | Sloc of Gnat_loc.loc
   | No_Info
(* The information that has been found in a node *)

let read_labels s =
   let b = { expl_loc    = None;
             expl_reason = None;
             expl_subp   = None ;
             expl_msg    = None } in
   Ident.Slab.iter
     (fun x ->
        let s = x.Ident.lab_string in
        if Util.starts_with s "GP_" then
           match Util.colon_split s with
           | ["GP_Reason"; reason] ->
                 b.expl_reason <- Some (reason_from_string reason)
           | ["GP_Pretty_Ada"; msg] ->
                 b.expl_msg <- Some msg
           | ["GP_Subp"; file; line] ->
                 begin try
                    b.expl_subp <-
                       Some (Gnat_loc.mk_loc_line file (int_of_string line))
                 with Failure "int_of_string" ->
                    Format.printf "GP_Subp: cannot parse string: %s" s;
                    Gnat_util.abort_with_message ""
                 end
           | "GP_Sloc" :: rest ->
                 begin try
                    b.expl_loc <- Some (Gnat_loc.parse_loc rest)
                 with Failure "int_of_string" ->
                    Format.printf "GP_Sloc: cannot parse string: %s" s;
                    Gnat_util.abort_with_message ""
                 end
           | _ ->
                 Gnat_util.abort_with_message
                     "found malformed GNATprove label"
     ) s;
     (* We potentially need to rectify in the case of loop invariants: We need
        to check whether the VC is for initialization or preservation *)
     if b.expl_reason = Some VC_Loop_Invariant then begin
        Ident.Slab.iter (fun x ->
           let s = x.Ident.lab_string in
           if Util.starts_with s "expl:" then
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
     match read_labels s with
     | { expl_loc = Some sloc ;
         expl_reason = Some reason;
         expl_subp = Some subp } ->
           Expl (mk_expl reason sloc subp)
     | { expl_loc = Some sloc ;
         expl_reason = _;
         expl_subp = _ ;
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
         read_labels t.t_label

let print_expl proven task fmt p =
   match p.loc with
   | [] -> assert false (* the sloc of a VC is never empty *)
   | primary :: secondaries ->
         if proven then begin
            Format.fprintf fmt "%a: info: %a proved"
            simple_print_loc primary print_reason p.reason
         end else begin
            let g = Task.task_goal_fmla task in
            let info = extract_msg g in
            let sloc =
               match info.expl_loc with
               | None -> primary
               | Some s -> List.hd s in
            Format.fprintf fmt "%a: %a not proved"
            simple_print_loc sloc print_reason p.reason;
            match info.expl_msg with
            | None -> ()
            | Some s -> Format.fprintf fmt ", requires %s" s
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
