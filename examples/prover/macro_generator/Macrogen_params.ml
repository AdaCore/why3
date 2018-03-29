
let (<<) f x = f x

open Macrogen_decls
open Format

module rec X : module type of Macrogen_params_sig = X
include X

module MakeDefaultP = functor (D0:Decls) -> struct
  
  include D0
  
  let variable_name tn fmt =
    fprintf fmt "Var_%s" << type_name dm tn
  
  let size_name tn fmt =
    fprintf fmt "size_%s" << type_name dm tn
  
  let nat_size_name tn fmt =
    fprintf fmt "nat_size_%s" << type_name dm tn
  
  let rename_name tn fmt =
    fprintf fmt "rename_%s" << type_name dm tn
  
  let size_lemma_name tn fmt =
    fprintf fmt "size_positive_lemma_%s" << type_name dm tn
  
  let subst_name tn fmt =
    fprintf fmt "subst_%s" << type_name dm tn
  
  let slift_name tn fmt =
    fprintf fmt "olifts_%s" << type_name dm tn
  
  let rename_subst_name tn fmt =
    fprintf fmt "rename_subst_%s" << type_name dm tn
  
  let subst_compose_name tn fmt =
    fprintf fmt "subst_compose_%s" << type_name dm tn
  
  let renaming_composition_lemma_name tn fmt =
    fprintf fmt "renaming_composition_lemma_%s" << type_name dm tn
  
  let rename_then_subst_composition_lemma_name tn fmt =
    fprintf fmt "rename_then_subst_composition_lemma_%s" << type_name dm tn
  
  let subst_then_rename_composition_lemma_name tn fmt =
    fprintf fmt "subst_then_rename_composition_lemma_%s" << type_name dm tn
  
  let subst_composition_lemma_name tn fmt =
    fprintf fmt "subst_composition_lemma_%s" << type_name dm tn
  
  let renaming_identity_lemma_name tn fmt =
    fprintf fmt "renaming_identity_lemma_%s" << type_name dm tn
  
  let subst_identity_lemma_name tn fmt =
    fprintf fmt "subst_identity_lemma_%s" << type_name dm tn
  
  let subst_identity_name tn fmt =
    fprintf fmt "subst_id_%s" << type_name dm tn
  
  let associativity_lemma_name (sub1,sub2,sub3) =
    let name = function true -> "subst" | false -> "rename" in
    let n1,n2,n3 = name sub1,name sub2,name sub3 in
    fun tn fmt ->
      fprintf fmt "associativity_%s_%s_%s_lemma_%s" n1 n2 n3 << type_name dm tn
  
  let right_rename_by_identity_lemma_name tn fmt =
    fprintf fmt "right_rename_subst_by_identity_lemma_%s" << type_name dm tn
  
  let right_subst_by_identity_lemma_name tn fmt =
    fprintf fmt "right_subst_subst_by_identity_lemma_%s" << type_name dm tn
  
  let left_rename_identity_lemma_name tn fmt =
    fprintf fmt "left_rename_subst_identity_lemma_%s" << type_name dm tn
  
  let left_subst_identity_lemma_name tn fmt =
    fprintf fmt "left_subst_subst_identity_lemma_%s" << type_name dm tn
  
  let slift_composition_lemma_name (b1,b2) tn fmt =
    let r b = if b then "subst" else "rename" in
    fprintf fmt "olifts_composition_lemma_%s_%s_%s"
      << r b1 << r b2 << type_name dm tn
  
  let subst_of_rename_name tn fmt =
    fprintf fmt "subst_of_rename_%s" << type_name dm tn
  
  let slift_identity_lemma_name tn fmt =
    fprintf fmt "olifts_identity_%s" << type_name dm tn
  
  let free_var_predicate_name tnv tn fmt =
    fprintf fmt "is_%s_free_var_in_%s" << type_name dm tnv << type_name dm tn
  
  let subst_free_var_inversion_helper_name sub tnv tn fmt =
    if sub
    then fprintf fmt "subst_free_var_constructive_inversion_%s_%s"
      << type_name dm tnv << type_name dm tn
    else fprintf fmt "rename_free_var_constructive_inversion_%s_%s"
      << type_name dm tnv << type_name dm tn
  
  let subst_free_var_inversion_lemma_name sub tnv tn fmt =
    if sub
    then fprintf fmt "subst_free_var_inversion_%s_%s"
      << type_name dm tnv << type_name dm tn
    else fprintf fmt "rename_free_var_inversion_%s_%s"
      << type_name dm tnv << type_name dm tn
  
  let rename_free_var_propagation_lemma_name tnv tn fmt =
    fprintf fmt "rename_free_var_propagation_%s_%s"
      << type_name dm tnv << type_name dm tn
  
  let subst_free_var_propagation_lemma_name tni tnv tn fmt =
    fprintf fmt "subst_free_var_propagation_%s_%s_%s"
      << type_name dm tni << type_name dm tnv << type_name dm tn
  
  let free_var_equivalence_lemma_name sub inv tn fmt =
    let p = if sub then "subst" else "rename" in
    fprintf fmt "free_var_%sequivalence_of_%s_%s"
      << (if inv then "derive_" else "")
      << p << type_name dm tn
  
  let close_name tnv tn fmt =
    fprintf fmt "close_%s_with_%s"
      << type_name dm tn << type_name dm tnv
  
  let openv_name tnv tn fmt =
    fprintf fmt "openv_%s_with_%s"
      << type_name dm tn << type_name dm tnv
  
  let opent_name tnv tn fmt =
    fprintf fmt "opent_%s_with_%s"
      << type_name dm tn << type_name dm tnv
  
  let size_preservation_lemma_name tn fmt =
    fprintf fmt "renaming_preserve_size_%s"
      << type_name dm tn
  
end

