(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*
  
*)

open Ident
open Term
open Decl

(* 
(* Debugging functions *)
let debug = Debug.register_info_flag "intro_projections_counterexmp"
  ~desc:"Print@ debugging@ messages@ about@ introducing@ projections@ for@ counterexamples."

let rec debug_print_terms terms =
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
let label_model = Ident.create_label "model"
(* Label for terms that should be projected in counterexample *)
let label_model_proj = Ident.create_label "model_projected"

(* Meta to tag projection functions *)
let meta_projection = Theory.register_meta "model_projection" [Theory.MTlsymbol]
  ~desc:"Declares@ the@ projection."

let intro_proj_for_ls map_projs ls_projected = 
  (* Returns list of declarations for projection of ls_projected
     if it has a  label "model_projected", otherwise returns [].

     The declarations include:
     - declaration of new constant with labels of ls_projected
       and label "model"
     - declaration of axiom saying that the new constant is equal to
       ls_projected projected by its projection function

     The projection function for ls_declared is stored in map_projs
     with key ls_projected.ls_value
  *)
  if not (Slab.mem label_model_proj ls_projected.ls_name.id_label) then
    []
  else
    match ls_projected.ls_value with
    | None -> []
    | Some ty_projected ->
      let create_proj_decls ls_projection =
	(* Creates declarations for projection of ls_projected using
	   projection function ls_projection. *)

	(* Create the projection *)
	let t_projected = Term.t_app ls_projected [] ls_projected.ls_value in
	let t_projection = Term.t_app ls_projection [t_projected] ls_projection.ls_value in
	
	(* Create declaration of new constant *)
	let name_new_constant = ls_projected.ls_name.id_string^"_proj_constant" in
	let lab_new = Slab.add label_model Slab.empty in
	let id_new = Ident.id_derive ~label:lab_new name_new_constant ls_projected.ls_name in
	let ls_new_constant =  Term.create_lsymbol id_new [] ls_projection.ls_value in
	let decl_new_constant = Decl.create_param_decl ls_new_constant in
	let t_new_constant = Term.t_app ls_new_constant [] ls_projection.ls_value in
	    
	(* Create the declaration of the axiom about the constant: t_new_constant = t_projection *)
	let name_axiom = ls_projected.ls_name.id_string^"_proj_axiom" in
	let id_axiom = Decl.create_prsymbol (Ident.id_fresh name_axiom) in
	let fla_axiom = Term.t_equ t_new_constant t_projection in
	let decl_axiom = Decl.create_prop_decl Decl.Paxiom id_axiom fla_axiom in
	    
	(* Add the declaration of new constant and the axiom *)
	decl_new_constant::decl_axiom::[]
      in
      try 
	let ls_proj = Ty.Mty.find ty_projected map_projs in
	create_proj_decls ls_proj
      with Not_found -> []
	
let introduce_projs map_projs decl =
  match decl.d_node with
  | Dparam ls_projected -> 
    (* Create declarations for a projection of ls_projected *)
    let projection_decls = intro_proj_for_ls map_projs ls_projected in
    decl::projection_decls

      (* TODO
  | Dlogic lslist -> 
    debug_decl decl;
    let new_decls = List.fold_left (fun list (ls,_) -> list @ (intro_proj_for_ls map_projs ls)) [] lslist in
    (* TODO *)
    [decl]
      *)
  | _ -> [decl]


let build_projections_map projs =
  (* Build map from types (Ty.ty) to projections (Term.lsymbol).
     The type t maps to the projection function f if f has a single
     argument of the type t.  
  *)
  let build_map ls_proj proj_map =
    match ls_proj.ls_args with
    | [ty_proj_arg] ->
      Ty.Mty.add ty_proj_arg ls_proj proj_map 
    | _ -> assert false
  in
  Sls.fold build_map projs Ty.Mty.empty

let meta_transform2 projs = 
  let map_projs = build_projections_map projs in
  Trans.decl (introduce_projs map_projs) None

let intro_projections_counterexmp = Trans.on_tagged_ls meta_projection meta_transform2

let () = Trans.register_transform "intro_projections_counterexmp" intro_projections_counterexmp
  ~desc:"Introduce@ new@ constant@ symbol@ for@ every@ term@ with@ model@ \
         label@ that@ has@ the@ same@ type@ as@ an@ argument@ of@ some@ function@ \
         labeled@ with@ meta@ model_projectionin@ the@ goal."

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
