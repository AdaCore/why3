
type printer = Format.formatter -> unit

open Macrogen_decls

module type NLParameters = sig
  
  val nlfree_var_type_name : TName.t -> printer
  val default_variable_value : TName.t -> printer
  val nltype_name : TName.t -> printer
  val free_variable_name : TName.t -> printer
  val bound_variable_name : TName.t -> printer
  val nlcons_name : CName.t -> printer
  val nlsize_name : TName.t -> printer
  val nat_nlsize_name : TName.t -> printer
  val nlsize_lemma_name : TName.t -> printer
  val shift_name : TName.t -> printer
  val shift_lemma_name : TName.t -> printer
  val model_name : TName.t -> printer
  val model_subst_commutation_lemma_name : TName.t -> printer
  val model_rename_commutation_lemma_name : TName.t -> printer
  val correct_indexes_name : TName.t -> printer
  val bound_depth_name : TName.t -> TName.t -> printer
  val bound_depth_lemma_name : TName.t -> TName.t -> printer
  val model_equal_lemma_name : TName.t -> printer
  val bind_var_name : TName.t -> TName.t -> printer
  val unbind_var_name : TName.t -> TName.t -> printer
  val subst_base_name : TName.t -> TName.t -> printer
  
  val impl_type_name : TName.t -> printer
  val data_field_name : TName.t -> printer
  val varset_type_name : TName.t -> printer
  val varset_field_name : TName.t -> TName.t -> printer
  val model_field_name : TName.t -> printer
  val invariant_name : TName.t -> printer
  val free_var_in_set_predicate : TName.t -> printer -> printer -> printer
  val varset_singleton : TName.t -> printer -> printer
  val varset_empty : TName.t -> printer
  val varset_join : TName.t -> printer -> printer -> printer
  val varset_fresh : TName.t -> printer -> printer
  val varset_add : TName.t -> printer -> printer -> printer
  val constructor_type_name : TName.t -> printer
  val constructor_variable_name : TName.t -> printer
  val constructor_cons_name : CName.t -> printer
  val constructor_invariant_name : TName.t -> printer
  val constructor_relation_name : TName.t -> printer
  val constructor_open_relation_name : TName.t -> printer
  val construction_operator_name : TName.t -> printer
  val destruction_operator_name : TName.t -> printer
  val subst_operator_name : TName.t -> TName.t -> printer
  
end

