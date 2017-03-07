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

open Ident
open Term
open Decl
open Theory
open Ty

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
  (* introduce new constant c and axiom stating c = t_rhs  *)
  let const_label = Slab.add model_label ls.ls_name.id_label in
  let const_label = append_to_model_element_name ~labels:const_label ~to_append:proj_name in
  let const_loc = Opt.get ls.ls_name.id_loc in
  let const_name = ls.ls_name.id_string^"_proj_constant_"^proj_name in
  let axiom_name = ls.ls_name.id_string^"_proj_axiom_"^proj_name in
  let id_new = Ident.id_user ~label:const_label const_name const_loc in
  intro_const_equal_to_term ~term:t_rhs ~id_new:id_new ~axiom_name:axiom_name

let get_record_field_suffix projection =
  try
    get_model_element_name ~labels:projection.ls_name.id_label
  with Not_found -> ""

(* Takes a type of map and returns the list of successive type in the map
   together with the return type. *)
let detect_map_types ty =
  let rec detect_map_types t_froms ty =
    match ty.ty_node with
    | Tyapp (ts, [t_from; t_to]) when ts.ts_name.id_string = "map" ->
        detect_map_types ((ts, t_from) :: t_froms) t_to
    | _ -> (List.rev t_froms, ty)
  in
  detect_map_types [] ty

(* Returns the return type of the last functions of list proj_functions *)
let rec last_type proj_functions =
  match proj_functions with
  | [] -> failwith "Should not happen. Please report."
  | [pf] -> (Opt.get pf.ls_value)
  | _pf1 :: pf2 :: tl -> last_type (pf2 :: tl)

(* Recreate type of the composition of projection functions *)
let recreate_types ty_froms proj_functions =
  let rec rec_types ty_froms =
  match ty_froms with
  | [(ts, ty_from)] ->
      ty_app ts [ty_from; last_type proj_functions]
  | (ts, ty_from) :: tl ->
      let ty_to = rec_types tl in
      ty_app ts [ty_from; ty_to]
  | [] -> failwith "Not a correct type application. Please report."
  in
  rec_types ty_froms

(* Returns a list of pairs of vsymbol for array axiom definition *)
let rec create_index_list ty_froms =
  match ty_froms with
  | ty :: tl ->
      let var_i : Term.vsymbol = Term.create_vsymbol (Ident.id_fresh "x") ty in
      let i : Term.term = Term.t_var var_i in
      let l = create_index_list tl in
      (var_i, i) :: l
  | [] -> []

(* Applying array to indices: term[i][j][k]....[w]...  *)
let rec recreate_term_applications select term var_l =
  match var_l with
  | i :: tl ->
      let term_x = Term.t_app_infer select [term;i] in
      recreate_term_applications select term_x tl
  | [] -> term

(* Generate the list of projections possible for a term where a possible projection is
   a list of functions that projects the result. *)
let rec list_projection_until_base_type map_projs t_to : Term.lsymbol list list =
  let proj_functions = try Some (Ty.Mty.find t_to map_projs)
  with | Not_found -> None in
  match proj_functions with
  | None -> [[]]
  | Some lpfs ->
    let lpfs_rec = List.map (fun x -> List.map (fun l -> x :: l)
        (list_projection_until_base_type map_projs (Opt.get x.ls_value)))
        lpfs in
    List.fold_left (fun acc x -> acc @ x) [] lpfs_rec

let rec projections_for_term ls term proj_name applied_projs env map_projs =
  (* Return declarations for projections of the term.
     Parameter proj_name is the name of the projection
     Parameter applied_proj_f is a set of projection functions already applied to the term *)
  match (Opt.get term.t_ty).ty_node with
  | Tyapp (ts, [_t_from; _t_to]) when ts.ts_name.id_string = "map" -> begin
      let (ty_froms, t_to) = detect_map_types (Opt.get term.t_ty) in
      let pfs =
        list_projection_until_base_type map_projs t_to
      in
      match pfs with
      | [] | [[]]->
         (* There is no projection function for the term
	    -> the projection consists of definition of constant c and axiom  c = p
	  *)
	  introduce_constant ls term proj_name
      | _ ->
          List.fold_left
	    (fun ldecls proj_function ->
	      (* Newly introduced map with projected indices *)
	      let proj_map_name = ls.ls_name.id_string^"_proj_arr_constant"^proj_name in
	      let proj_map_id = Ident.id_fresh proj_map_name in
	      let proj_map_ty = Some (recreate_types ty_froms proj_function) in
	      let proj_map_ls = Term.create_lsymbol proj_map_id [] proj_map_ty in
	      let proj_map_decl = Decl.create_param_decl proj_map_ls in
	      let proj_map_t = Term.t_app proj_map_ls [] proj_map_ty in

              (* The quantified variables i's *)
              let var_l = create_index_list (List.map snd ty_froms) in

	      let map_theory = Env.read_theory env ["map"] "Map" in
	      let select = (ns_find_ls map_theory.th_export ["get"]) in

              (* Indices: proj_map[i], term[i]  *)
	      let term_idx_comp_app = recreate_term_applications select term (List.map snd var_l) in
              let proj_map_idx_comp_app = recreate_term_applications select proj_map_t (List.map snd var_l) in

	      (* Formula f: forall i : t_from. proj_map[i] = pf_1(term[i]) *)
	      let term_idx_projected_t : Term.term =
                List.fold_left (fun term_idx_comp_app proj_function ->
                 Term.t_app proj_function [term_idx_comp_app] proj_function.ls_value)
                   term_idx_comp_app proj_function in
              let fla_to_be_quant = Term.t_equ proj_map_idx_comp_app term_idx_projected_t in
              let fla_axiom = Term.t_forall_close (List.map fst var_l) [] fla_to_be_quant in

	      (* Axiom about projection: axiom f *)
	      let proj_axiom_name = ls.ls_name.id_string^"_proj_arr_axiom"^proj_name in
	      let proj_axiom_id = Decl.create_prsymbol (Ident.id_fresh proj_axiom_name) in
	      let proj_axiom = Decl.create_prop_decl Decl.Paxiom proj_axiom_id fla_axiom in

	      (* Recursively call projecting of the term proj_map -> proj_map_projections  *)
	      let proj_name = proj_name^(List.fold_left
                 (fun acc x -> acc ^ get_record_field_suffix x)
                    "" proj_function) in
	      (*let applied_projs = Term.Sls.add proj_function applied_projs in*)
	      let proj_map_projections_defs =
                introduce_constant ls proj_map_t proj_name in
              ldecls @ [proj_map_decl;proj_axiom] @ proj_map_projections_defs
            )
	    []
	    pfs
  end

  | _ ->
   (* Non-map case *)
      (* Find all projection functions for the term *)
      let pfs = try (Some (Ty.Mty.find (Opt.get term.t_ty) map_projs)) with
      | Not_found -> None in
      match pfs with
      | None ->
          (* There is no projection function for the term
	    -> the projection consists of definition of constant c and axiom  c = p
	  *)
	  introduce_constant ls term proj_name
      | Some pfs ->
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
  if not (Slab.mem model_proj_label ls_projected.ls_name.id_label) then
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

      (* TODO
  | Dlogic lslist ->
    debug_decl decl;
    let new_decls = List.fold_left (fun list (ls,_) -> list @ (intro_proj_for_ls map_projs ls)) [] lslist in
    (* TODO *)
    [decl]
      *)
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
