(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Decl
open Term
open Ident

(** For see intro_vc_vars_counterexmp.mli for detailed description
    of this transformation. *)

let meta_vc_location =
  Theory.register_meta_excl "vc_location" [Theory.MTstring]
  ~desc:"Location@ of@ the@ term@ that@ triggers@ vc@ in@ the@ form@ file:line:col."

let model_label = Ident.create_label "model"
  (* Identifies terms that should be in counterexample and should not be projected. *)
let model_projected_label = Ident.create_label "model_projected"
  (* Identifies terms that should be in counterexample and should be projected. *)
let model_vc_label = Ident.create_label "model_vc"
  (* Identifies the term that triggers the VC. *)
let model_vc_post_label = Ident.create_label "model_vc_post"
(* Identifies the postcondition that triggers the VC. *)
let model_trace_prefix = "model_trace:"
  (* The term labeled with "model_trace:name" will be in counterexample with name "name" *)

(* Information about the term that triggers VC.  *)
type vc_term_info = {
  mutable vc_inside : bool;
  (* true if the term that triggers VC is currently processed *)
  mutable vc_loc : Loc.position option;
  (* the position of the term that triggers VC *)
  mutable vc_pre_or_post : bool;
  (* true if VC was generated for precondition or postcondition *)
}

let get_label labels prefix =
  let check l = Strings.has_prefix prefix l.lab_string in
  Slab.choose (Slab.filter check labels)

let is_model_vc_label l =
  lab_equal l model_vc_label || lab_equal l model_vc_post_label

let check_enter_vc_term t info =
  (* Check whether the term that triggers VC is entered.
     If it is entered, extract the location of the term and if the VC is
     postcondition or precondition of a function, extract the name of
     the corresponding function.
  *)
  if Slab.exists is_model_vc_label t.t_label then begin
    info.vc_inside <- true;
    info.vc_loc <- t.t_loc;
    info.vc_pre_or_post <- Slab.mem model_vc_post_label t.t_label;
  end

let check_exit_vc_term t info =
  (* Check whether the term triggering VC is exited. *)
  if Slab.exists is_model_vc_label t.t_label then begin
    info.vc_inside <- false;
  end

(* TODO: add "remove_suffix" to Strings and use it here instead of regexps *)
let add_old lab_str =
  try
    let pos = Str.search_forward (Str.regexp "@") lab_str 0 in
    let after = String.sub lab_str pos ((String.length lab_str)-pos) in
    if after = "@init" then
      (String.sub lab_str 0 pos) ^ "@old"
    else lab_str
  with Not_found -> lab_str ^ "@old"

let model_trace_for_postcondition ~labels =
  (* Modifies the  model_trace label of a term in the postcondition:
     - if term corresponds to the initial value of a function
     parameter, model_trace label will have postfix @old

     Returns labels with model_trace label modified if there
     exist model_trace label in labels, labels otherwise.
  *)
  try
    let trace_label = get_label labels model_trace_prefix in
    let lab_str = add_old trace_label.lab_string in
    if lab_str = trace_label.lab_string then
      labels
    else
      let other_labels = Slab.remove trace_label labels in
      Slab.add
	(Ident.create_label lab_str)
	other_labels
  with Not_found ->
    labels

let rec do_intro info t =
  check_enter_vc_term t info;

  let defs = match t.t_node with
    | Tapp (ls, tl) ->
      begin
	match tl with
	| [] ->
	  if info.vc_inside then begin
	    match info.vc_loc with
	    | None -> []
	    | Some loc ->
	      (* variable inside the term T that triggers VC.
		 If the variable should be in counterexample, introduce new constant
		 in location loc with all labels necessary for collecting the it for
		 counterexample and make it equal to the variable *)
	      let is_counterexample_label l = if
		  l = model_label || l = model_projected_label then true else false in
	      if Slab.exists is_counterexample_label ls.ls_name.id_label then
		let const_label = if info.vc_pre_or_post then
		    model_trace_for_postcondition ~labels:ls.ls_name.id_label
		  else
		    ls.ls_name.id_label in
		let const_name = ls.ls_name.id_string^"_vc_constant" in
		let axiom_name = ls.ls_name.id_string^"_vc_axiom" in
		Intro_projections_counterexmp.intro_const_equal_to_term
		  ~term:t ~const_label ~const_loc:loc ~const_name ~axiom_name
	      else
		[]
	  end
	  else []
	| _ ->
	  List.fold_left
	    (fun defs term ->
	      List.append defs (do_intro info term))
	    []
	    tl
      end;
    | Tbinop (_, f1, f2) ->
      List.append (do_intro info f1) (do_intro info f2)
    | Tquant (_, fq) ->
      let _, _, f = t_open_quant fq in
      do_intro info f
    | Tlet (t, tb) ->
      let _, f = t_open_bound tb in
      List.append (do_intro info t) (do_intro info f)
    | Tnot f ->
      do_intro info f
    | Tif (f1, f2, f3) ->
      List.append
	(List.append (do_intro info f1) (do_intro info f2))
	(do_intro info f3)
    | Tcase (t, _) ->
      do_intro info t
      (* todo: handle the second argument of Tcase *)
    | _ -> [] in

  check_exit_vc_term t info;

  defs

let do_intro_vc_vars_counterexmp info pr f =
  List.append (do_intro info f) [(create_prop_decl Pgoal pr f)]

let intro_vc_vars_counterexmp2 task =
  let info = {
    vc_inside = false;
    vc_loc = None;
    vc_pre_or_post = false;
  } in
  (* Do introduction and find location of term triggering VC *)
  let do_intro_trans = Trans.goal (do_intro_vc_vars_counterexmp info) in
  let task = (Trans.apply do_intro_trans) task in

  (* Pass meta with location of the term triggering VC to printer  *)
  let vc_loc_meta = Theory.lookup_meta "vc_location" in
  let g,task = Task.task_separate_goal task in
  let pos_str = match info.vc_loc with
    | None -> ""
    | Some loc ->
      let (file, line, col1, col2) = Loc.get loc in
      file ^ ":" ^ (string_of_int line) ^ ":" ^ (string_of_int col1) ^ ":" ^ (string_of_int col2)
  in
  let task = Task.add_meta task vc_loc_meta [Theory.MAstr pos_str] in
  Task.add_tdecl task g

let intro_vc_vars_counterexmp = Trans.store intro_vc_vars_counterexmp2

let () = Trans.register_transform "intro_vc_vars_counterexmp"
  intro_vc_vars_counterexmp
  ~desc:"Introduce."

let get_location_of_vc task =
  let meta_args = Task.on_meta_excl meta_vc_location task in
  match meta_args with
  | Some [Theory.MAstr loc_str] ->
    (* There may be colons in the file name. We still split on the colon, look at
       the last three elements, and put the remaining ones back together to form the
       file name. We may lose colons at the beginning or end of the filename, but
       even on windows that's not allowed. *)
    let split = Strings.rev_split ':' loc_str in
    let loc =  match split with
      | col2 :: col1 :: line :: ((_ :: _) as rest) ->
	let line = int_of_string line in
	let col1 = int_of_string col1 in
	let col2 = int_of_string col2 in
	let filename = Strings.join ":" (List.rev rest) in
        Some (Loc.user_position filename line col1 col2)
      | _ -> None in
    loc
  | _ -> None
