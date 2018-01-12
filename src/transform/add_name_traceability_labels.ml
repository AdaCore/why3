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

(*
The transformation that adds labels with information needed for
traceability from the names in the Why output to names in the
Why input (more precisely to the names that are present
at the time this transformation is run).

This transformation should be called on the AST corresponding to
the Why input. For each element it adds the label with the information
about the name of the element.  
*)

open Term
open Ident
open Format

let debug = Debug.register_info_flag "add_name_traceability"
  ~desc:"Print@ debugging@ messages@ about@ adding@ traceability@ labels."

let term2string_experimental t =
  (* TODO: Pretty.print_term prints also labels + it generates unique identifiers when printing *)
  Pretty.print_term str_formatter t;
  flush_str_formatter ()

(* TODO: should print the term *)
let term2string t = "term"

let create_traceability_label str =
  Ident.create_label ("model_trace:"^str)

let create_traceability_identifier ident =
  id_clone ~label:(Slab.singleton (create_traceability_label ident.id_string))  ident

(*Adds name traceability label to the list of terms. *)
let rec add_traceability_label_list terms collected_terms =
  match terms with
  | [] -> List.rev collected_terms
  | t::tail ->
    let t_traceable = add_traceability_label t in
    add_traceability_label_list tail (t_traceable::collected_terms)
(* Adds name traceability label to the term. *)
and  add_traceability_label t = 
  let term = match t.t_node with
    |Tvar v ->
      Debug.dprintf debug "Adding traceability labels: variable@.";
      let vs_name_t = create_traceability_identifier v.vs_name in
      Debug.dprintf debug "Creating vsymbol@.";
      let v_t = create_vsymbol vs_name_t v.vs_ty in
      Debug.dprintf debug "Creating t_var@.";
      (* TODO: The following does not work - investigate. *)
      (* t_var v_t *)
      t_var v
    | Tapp (l_symb, terms) ->
      Debug.dprintf debug "Adding traceability labels: Tapp@.";
      let l_symb_name = create_traceability_identifier l_symb.ls_name in
      let l_symb_t = create_lsymbol l_symb_name l_symb.ls_args l_symb.ls_value in
      let terms_t = add_traceability_label_list terms [] in
      t_app l_symb terms_t t.t_ty
    | Tif (t1, t2, t3) ->
      Debug.dprintf debug "Adding traceability labels: Tif@.";
      let t1t = add_traceability_label t1 in
      let t2t = add_traceability_label t2 in
      let t3t = add_traceability_label t3 in
      t_if t1t t2t t3t
    | Tlet (t, t_bound) ->
      Debug.dprintf debug "Adding traceability labels: Tlet@.";
      let tt = add_traceability_label t in
      let vs_bound, term_bound = t_open_bound t_bound in
      let vs_boundt = vs_bound in (* TODO *)
      let term_boundt = add_traceability_label term_bound in
      let t_boundt = t_close_bound vs_boundt term_boundt in
      t_let tt t_boundt
    | Tcase (t, tbs) ->
      (* TODO *)
      t
    | Teps tb ->
      (* TODO *)
      t
    | Tquant (q, fq) ->
      let vl, tl, f = t_open_quant fq in
      let ft = add_traceability_label f in
      (* TODO tl, vl *)
      t_quant_close q vl tl ft
    | Tbinop (op, f1, f2) -> 
      Debug.dprintf debug "Adding traceability labels: binary operation@.";
      let f1_t = add_traceability_label f1 in
      let f2_t = add_traceability_label f2 in
      t_binary op f1_t f2_t
    | Tnot t ->
      (* TODO *)
      t
    | _ ->
      Debug.dprintf debug "Adding traceability labels: unsupported term@.";
      t 
  in
  let term = t_label_copy t term in
  Debug.dprintf debug "Adding label to toplevel term@.";
  t_label_add (create_traceability_label (term2string t)) term

let add_traceability_labels = Trans.rewrite add_traceability_label None

let () =
  Trans.register_transform "add_name_traceability_labels" add_traceability_labels
    ~desc:"Add@ labels@ to@ terms@ used@ in@ counterexample@ report@ holding information@ needed@ for@ traceability@ of@ identifiers'@ names.";
