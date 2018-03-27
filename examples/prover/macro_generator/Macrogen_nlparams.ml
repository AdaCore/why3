
let (<<) f x = f x

open Macrogen_decls
open Macrogen_params
open Format

module rec X : module type of Macrogen_nlparams_sig = X
include X

module MakeDefaultP = functor (D0:Decls) -> struct
  
  open D0
  
  let nlfree_var_type_name _ fmt = fprintf fmt "int"
  
  let default_variable_value _ fmt = fprintf fmt "(-1)"
  
  let nltype_name tn fmt =
    fprintf fmt "nl_%s"
      << type_name dm tn
  
  let free_variable_name tn fmt =
    fprintf fmt "NLFVar_%s"
      << type_name dm tn
  
  let bound_variable_name tn fmt =
    fprintf fmt "NLBruijn_%s"
      << type_name dm tn
  
  let nlcons_name cn fmt =
    fprintf fmt "NL_%s"
      << cons_name dm cn
  
  let nlsize_name tn fmt =
    fprintf fmt "nlsize_%s"
      << type_name dm tn
  
  let nat_nlsize_name tn fmt =
    fprintf fmt "nat_nlsize_%s"
      << type_name dm tn
  
  let nlsize_lemma_name tn fmt =
    fprintf fmt "nlsize_positive_lemma_%s"
      << type_name dm tn
  
  let shift_name tn fmt =
    fprintf fmt "shiftb_%s"
      << type_name dm tn
  
  let shift_lemma_name tn fmt =
    fprintf fmt "shiftb_compose_lemma_%s"
      << type_name dm tn
  
  let model_name tn fmt =
    fprintf fmt "nlmodel_%s"
      << type_name dm tn
  
  let model_subst_commutation_lemma_name tn fmt =
    fprintf fmt "nlmodel_subst_commutation_lemma_%s"
      << type_name dm tn
  
  let model_rename_commutation_lemma_name tn fmt =
    fprintf fmt "nlmodel_rename_commutation_lemma_%s"
      << type_name dm tn
  
  let correct_indexes_name tn fmt =
    fprintf fmt "correct_indexes_%s" << type_name dm tn
  
  let bound_depth_name tnv tn fmt =
    fprintf fmt "bound_depth_of_%s_in_%s"
      << type_name dm tnv << type_name dm tn
  
  let bound_depth_lemma_name tnv tn fmt =
    fprintf fmt "bound_depth_of_%s_in_%s_nonnegative"
      << type_name dm tnv << type_name dm tn
  
  let model_equal_lemma_name tn fmt =
    fprintf fmt "model_equal_%s"
      << type_name dm tn
  
  let bind_var_name tnv tn fmt =
    fprintf fmt "bind_var_%s_in_%s"
      << type_name dm tnv << type_name dm tn
  
  let unbind_var_name tnv tn fmt =
    fprintf fmt "unbind_var_%s_in_%s"
      << type_name dm tnv << type_name dm tn
  
  let subst_base_name tnv tn fmt =
    fprintf fmt "subst_base_%s_in_%s"
      << type_name dm tnv << type_name dm tn
  
  let impl_type_name tn fmt =
    fprintf fmt "nlimpl_%s" << type_name dm tn
  
  let data_field_name tn fmt =
    fprintf fmt "nlrepr_%s_field" << type_name dm tn
  
  let varset_type_name _ fmt =
    fprintf fmt "int"
  
  let varset_field_name tnv tn fmt =
    fprintf fmt "nlfree_var_%s_set_abstraction_%s_field"
      << type_name dm tnv << type_name dm tn
  
  let model_field_name tn fmt =
    fprintf fmt "model_%s_field" << type_name dm tn
  
  let invariant_name tn fmt =
    fprintf fmt "%t_ok" << impl_type_name tn
  
  let free_var_in_set_predicate _ p1 p2 fmt =
    fprintf fmt "(%t)@ <@ (%t)" p1 p2
  
  let varset_singleton _ p1 fmt =
    fprintf fmt "(" ;
    pp_open_box fmt indent ;
    fprintf fmt "1@ +@ (%t)@])" p1
  
  let varset_empty _ fmt = fprintf fmt "0"
  
  (*let varset_join _ p1 p2 fmt =
    let indent fmt = pp_open_box fmt indent in
    fprintf fmt "(%t%tlet@ a@ =@ (%t)@]@ in@ \
      %tlet@ b@ =@ (%t)@]@ in@ \
      %tif a < b@ then b@ else a@]@])"
      indent indent p1 indent p2 indent*)
  
  (* For some reason, this version generates a
     VERY different wp structure ! *)
  let varset_join _ p1 p2 fmt =
    let indent fmt = pp_open_box fmt indent in
    fprintf fmt "(%t%tlet@ aux@ (a:int)@ (b:int) :@ int@ \
      %tensures@ {@ %tresult@ >=@ a@]@ /\\@ %tresult@ >=@ b@]@ }@]@ \
      =@ %tif a < b@ then b@ else a@]@]@ in@ %taux@ (%t)@ (%t)@]@])"
      indent indent indent indent indent indent indent p1 p2
  
  let varset_fresh _ p = p
  
  let varset_add tn p1 p2 fmt =
    varset_join tn (varset_singleton tn p1) p2 fmt
  
  let constructor_type_name tn fmt =
    fprintf fmt "cons_%s" << type_name dm tn
  
  let constructor_variable_name tn fmt =
    fprintf fmt "NLCVar_%s" << type_name dm tn
  
  let constructor_cons_name cn fmt =
    fprintf fmt "NLC_%s" << cons_name dm cn
  
  let constructor_invariant_name tn fmt =
    fprintf fmt "cons_ok_%s" << type_name dm tn
  
  let constructor_relation_name tn fmt =
    fprintf fmt "cons_rel_%s" << type_name dm tn
  
  let constructor_open_relation_name tn fmt =
    fprintf fmt "cons_open_rel_%s" << type_name dm tn
  
  let construction_operator_name tn fmt =
    fprintf fmt "construct_%s" << type_name dm tn
  
  let destruction_operator_name tn fmt =
    fprintf fmt "destruct_%s" << type_name dm tn
  
  let subst_operator_name tnv tn fmt =
    fprintf fmt "nlsubst_%s_in_%s" << type_name dm tnv << type_name dm tn
  
end

