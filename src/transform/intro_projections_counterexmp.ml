(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Term
open Decl
open Theory
open Ty

let model_trace_regexp = Str.regexp "model_trace:"
  (* The term labeled with "model_trace:name" will be in counterexample with name "name" *)


let label_starts_with regexp l =
  try
    ignore(Str.search_forward regexp l.lab_string 0);
    true
  with Not_found -> false

let string_starts_with regexp l =
  try
    ignore(Str.search_forward regexp l 0);
    true
  with Not_found -> false

let get_label labels regexp =
  Slab.choose (Slab.filter (label_starts_with regexp) labels)

let is_proj_for_array_attr proj_name =
  let b =
    try
      string_starts_with (Str.regexp "'First\\|'Last\\|\\.") proj_name
    with Not_found -> false in
  b



(*
(* Debugging functions *)
let debug = Debug.register_info_flag "intro_projections_counterexmp"
  ~desc:"Print@ debugging@ messages@ about@ introducing@ projections@ for@ counterexamples."

vlet rec debug_print_terms terms =
  match terms with
  | [] -> ()
  | term::tail ->

    Pretty.print_term Format.str_formatter term;
    debug_print_terms tail

let debug_decl decl =
  Pretty.print_decl Format.str_formatter decl;
  let s = Format.flush_str_formatter () in
  Debug.dprintf debug "Declaration %s @." s
*)

(* Label for terms that should be in counterexample *)
let model_label = Ident.create_label "model"
(* Label for terms that should be projected in counterexample *)
let model_proj_label = Ident.create_label "model_projected"

(* Meta to tag projection functions *)
let meta_projection = Theory.register_meta "model_projection" [Theory.MTlsymbol]
  ~desc:"Declares@ the@ projection."

let intro_const_equal_to_term
    ~term
    ~id_new
    ~axiom_name
    =
  (* See documentation of the function in file intro_projections_counterexmp.mli. *)

  (* Create declaration of new constant *)
  (*let lab_new = Slab.add model_label labels in*)
  let ls_new_constant =  Term.create_lsymbol id_new [] term.t_ty in
  let decl_new_constant = Decl.create_param_decl ls_new_constant in
  let t_new_constant = Term.t_app ls_new_constant [] term.t_ty in

  (* Create declaration of the axiom about the constant: t_new_constant = t_rhs *)
  let id_axiom = Decl.create_prsymbol (Ident.id_fresh axiom_name) in
  let fla_axiom = Term.t_equ t_new_constant term in
  let decl_axiom = Decl.create_prop_decl Decl.Paxiom id_axiom fla_axiom in

  (* Return the declaration of new constant and the axiom *)
  decl_new_constant::decl_axiom::[]

let introduce_constant ls t_rhs proj_name =
  (* We only allow projections to apply if they produce an element with a new
     model trace. In practice, we forbid proj_name that are not record (".") or
     array attributes like First and Last *)
  if is_proj_for_array_attr proj_name then
    (* introduce new constant c and axiom stating c = t_rhs  *)
    let const_label = Slab.add model_label ls.ls_name.id_label in
    let const_label = append_to_model_element_name ~labels:const_label ~to_append:proj_name in
    let const_loc = Opt.get ls.ls_name.id_loc in
    let const_name = ls.ls_name.id_string^"_proj_constant_"^proj_name in
    let axiom_name = ls.ls_name.id_string^"_proj_axiom_"^proj_name in
    let id_new = Ident.id_user ~label:const_label const_name const_loc in
    intro_const_equal_to_term ~term:t_rhs ~id_new:id_new ~axiom_name:axiom_name
  else
    []

let get_record_field_suffix projection =
  try
    get_model_element_name ~labels:projection.ls_name.id_label
  with Not_found -> ""

(* Find the projections corresponding to some type if it exists *)
let get_list_projs t map_projs =
  match t.t_ty with
  | None -> []
  | Some ty ->
      let pfs = try Ty.Mty.find ty map_projs with | Not_found -> [] in
      pfs

let rec projections_for_term ls term proj_name applied_projs env map_projs =
  (* Return declarations for projections of the term.
     Parameter proj_name is the name of the projection
     Parameter applied_proj_f is a set of projection functions already applied
     to the term *)
  match (Opt.get term.t_ty).ty_node with
  | Tyapp (ts, [_t_from; _t_to]) when ts.ts_name.id_string = "map" -> begin
      let pfs = get_list_projs term map_projs in
      match pfs with
      | [] ->
          (* There is no projection function for the term
             -> the projection consists of definition of constant c and axiom  c = p
           *)
          introduce_constant ls term proj_name
      | _ ->
          List.fold_left
            (fun ldecls proj_function ->
              let rhs = Term.t_app_infer proj_function [(Term.t_app_infer ls [])] in
              let l = introduce_constant ls rhs proj_name in
              ldecls @ l
            )
            []
            pfs
  end

  | _ ->
   (* Non-map case *)
      (* Find all projection functions for the term *)
      let pfs = get_list_projs term map_projs in
      match pfs with
      | [] ->
          (* There is no projection function for the term
	    -> the projection consists of definition of constant c and axiom  c = p
	  *)
	  introduce_constant ls term proj_name
      | pfs ->
	(* Collect declarations for projections f of the form
	   f = pf_n .. pf_1 where pf_1 is an element of pfs *)
	List.fold_left
	  (fun l pf_1 ->
	    if Term.Sls.mem pf_1 applied_projs then
	      (* Do not apply the same projection twice *)
	      l @ introduce_constant ls term proj_name
	    else
	      let t_applied = Term.t_app pf_1 [term] pf_1.ls_value in
	      let proj_name = proj_name^(get_record_field_suffix pf_1) in
	      let applied_projs = Term.Sls.add pf_1 applied_projs in
	      (* Return declarations for projections of t_applied = pf_1 term *)
	      let t_applied_projs =
                projections_for_term ls t_applied proj_name applied_projs env map_projs in
              l @ t_applied_projs
	  )
	  []
	  pfs

let intro_proj_for_ls env map_projs ls_projected =
  (* Returns list of declarations for projection of ls_projected
     if it has a  label "model_projected", otherwise returns [].

     There can be more projections for ls_projected. For each projection
     f the declarations include:
     - declaration of new constant with labels of ls_projected, label "model",
       and label "model_trace:proj_name" where proj_name is the name of the projection
     - declaration of axiom saying that the new constant is equal to
       ls_projected projected by its projection

     The projection is composed from projection functions stored in
     map_projs.

     @param map_projs maps types to projection function for these types
     @param ls_projected the label symbol that should be projected
  *)
  if not (Slab.mem model_proj_label ls_projected.ls_name.id_label)
  then
    (* ls_projected has not a label "model_projected" *)
    []
  else
    match ls_projected.ls_value with
    | None -> []
    | Some _ ->

      (* Create term from ls_projected *)
      let t_projected = Term.t_app ls_projected [] ls_projected.ls_value in
      projections_for_term ls_projected t_projected "" Term.Sls.empty env map_projs

let introduce_projs env map_projs decl =
  match decl.d_node with
  | Dparam ls_projected ->
    (* Create declarations for a projections of ls_projected *)
    let projection_decls = intro_proj_for_ls env map_projs ls_projected in
    projection_decls

  | _ -> []

let introduce_projs env map_projs decl =
  match decl with
  | Decl d -> introduce_projs env map_projs d
  | _ -> []

let build_projections_map projs =
  (* Build map from types (Ty.ty) to projections (Term.lsymbol).
     The type t maps to the projection function f if f has a single
     argument of the type t.
  *)
  let build_map ls_proj proj_map =
    match ls_proj.ls_args with
    | [ty_proj_arg] ->
      let projs_for_ty =
	try
	  Ty.Mty.find ty_proj_arg proj_map
	with Not_found -> []
      in
      let projs_for_ty = ls_proj :: projs_for_ty in
      Ty.Mty.add ty_proj_arg projs_for_ty proj_map
    | _ -> assert false
  in
  Sls.fold build_map projs Ty.Mty.empty

(* TODO we want to be able to write this. It seems not possible with Trans and
   more efficient than the version we have below.
let meta_transform2 f : Task.task -> Task.task = fun task ->
  Trans.apply (Trans.fold (fun d t ->
    Trans.apply (Trans.add_decls (f d)) t) task) task
*)

(* [meta_transform2 f t] Generate new declarations by applying f to each declaration of t
   and then append these declarations to t *)
let meta_transform2 f : Task.task Trans.trans =
  let list_decl = Trans.fold (fun d l -> l @ (f d)) [] in
  Trans.bind list_decl (fun x -> Trans.add_decls x)

let encapsulate env projs : Task.task Trans.trans =
  let map_projs = build_projections_map projs in
  meta_transform2 (fun d -> introduce_projs env map_projs d.Task.task_decl.td_node)

let intro_projections_counterexmp env =
  Trans.on_tagged_ls meta_projection (encapsulate env)


let () = Trans.register_env_transform "intro_projections_counterexmp" intro_projections_counterexmp
  ~desc:"For@ each@ declared@ abstract@ function@ and@ predicate@ p@ with@ label@ model_projected@ \
and@ projectin@ f@ for@ p@ creates@ declaration@ of@ new@ constant@ c@ with@ label@ model@ and@ an@ axiom@ \
c = f p."

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
