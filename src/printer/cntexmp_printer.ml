(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Term


(* Information about the term that triggers VC.  *)
type vc_term_info = {
  mutable vc_inside : bool;
  (* true if the term that triggers VC is currently processed *)
  mutable vc_loc : Loc.position option;
  (* the position of the term that triggers VC *)
  mutable vc_func_name : string option;
  (* the name of the function for that VC was made. None if VC
     is not generated for postcondition or precondition) *)
}

module TermCmp = struct
  type t = term

  let before loc1 loc2 =
  (* Return true if loc1 is strictly before loc2 *)
    match loc1 with
    | None -> false
    | Some loc1 ->
      match loc2 with
      | None -> false
      | Some loc2 ->
	let (_, line1, col1, _) = Loc.get loc1 in
	  let (_, line2, col2, _) = Loc.get loc2 in
	  if line1 <> line2 then
	    if line1 < line2 then true
	    else false
	  else
	    if col1 < col2 then true
	    else false

  let compare a b =
    if (a.t_loc = b.t_loc) && (a.t_label = b.t_label)
    then 0 else
      (* Order the terms accoridng to their source code locations  *)
      if before a.t_loc b.t_loc then 1
      else -1

end

module S = Set.Make(TermCmp)

let add_model_element (el: term) info_model =
 (* Add element el (term) to info_model.
    If an element with the same hash (the same set of labels + the same
    location) as the element el already exists in info_model, replace it with el.

    The reason is that  we do not want to display two model elements with the same
    name in the same location and usually it is better to display the last one.

    Note that two model elements can have the same name and location if why is used
    as an intemediate language and the locations are locations in the source language.
    Then, more why constructs (terms) can represent a single construct in the source
    language and more terms have thus the same model name and location. This happens,
    e.g., if why code is generated from SPARK. There, the first iteration of while
    cycle is unrolled in some cases. If the task contains both a term representing a
    variable in the first iteration of unrolled loop and a term representing the variable
    in the subsequent loop iterations, only the latter is relevant for the counterexample
    and it is the one that comes after the former one (and that is why we always keep the
    last term).
*)
  let info_model = S.remove el info_model in
  S.add el info_model

let add_old lab_str =
  try
    let pos = Str.search_forward (Str.regexp "@") lab_str 0 in
    let after = String.sub lab_str pos ((String.length lab_str)-pos) in
    if after = "@init" then
      (String.sub lab_str 0 pos) ^ "@old"
    else lab_str
  with Not_found -> lab_str ^ "@old"

let model_trace_for_postcondition ~labels (info: vc_term_info)  =
  (* Modifies the  model_trace label of a term in the postcondition:
     - if term corresponds to the initial value of a function
     parameter, model_trace label will have postfix @old
     - if term corresponds to the return value of a function, add
     model_trace label in a form function_name@result
  *)
  try
    let trace_label = get_model_trace_label ~labels in
    let lab_str = add_old trace_label.lab_string in
    if lab_str = trace_label.lab_string then
      labels
    else
      let other_labels = Slab.remove trace_label labels in
      Slab.add
	(Ident.create_label lab_str)
	other_labels
  with Not_found ->
    (* no model_trace label => the term represents the return value *)
    Slab.add
      (Ident.create_model_trace_label
	 ((Opt.get_def "" info.vc_func_name)  ^ "@result"))
      labels

let get_fun_name name =
  let splitted = Strings.bounded_split ':' name 2 in
  match splitted with
  | _::[second] ->
    second
  | _ ->
    ""

let check_enter_vc_term t in_goal vc_term_info =
  (* Check whether the term that triggers VC is entered.
     If it is entered, extract the location of the term and if the VC is
     postcondition or precondition of a function, extract the name of
     the corresponding function.
  *)
  if in_goal && Slab.mem Ident.model_vc_label t.t_label then begin
    vc_term_info.vc_inside <- true;
    vc_term_info.vc_loc <- t.t_loc;
    try
      (* Label "model_func" => the VC is postcondition or precondition *)
      (* Extract the function name from "model_func" label *)
      let fun_label =
        Slab.choose (Slab.filter (fun l -> Strings.has_prefix "model_func:" l.lab_string)
                                 t.t_label)
      in
      vc_term_info.vc_func_name <- Some (get_fun_name fun_label.lab_string);
    with Not_found ->
      (* No label "model_func" => the VC is not postcondition or precondition *)
      ()
  end

let check_exit_vc_term t in_goal info =
  (* Check whether the term triggering VC is exited. *)
  if in_goal && Slab.mem Ident.model_vc_label t.t_label then begin
    info.vc_inside <- false;
  end
