
open Macrogen_nlparams
open Macrogen_decls
open Macrogen_printing

module Printer : functor (P:PrintParameters) ->
  functor (NLP:NLParameters) -> sig
  
  val type_defs_printer : printer
  val size_defs_printer : printer
  val size_lemma_printer : printer
  val shift_defs_printer : printer
  val shift_lemma_printer : printer
  val model_defs_printer : printer
  val model_subst_commutation_lemma_printer : printer
  val model_rename_commutation_lemma_printer : printer
  val correct_indexes_printer : printer
  val bound_depth_printer : printer
  val bound_depth_lemma_printer : printer
  val model_equal_lemma_printer : printer
  val bind_var_printer : printer
  val unbind_var_printer : printer
  
  val implementation_type_printer : printer
  val invariant_printer : printer
  val constructor_type_printer : printer
  val constructor_invariant_printer : printer
  val constructor_relation_printer : printer
  val constructor_open_relation_printer : printer
  val construction_operator_printer : printer
  val destruction_operator_printer : printer
  val subst_operator_printer : printer
  
  
  val types_defs_printer : printer
  val logics_defs_printer : printer
  val impls_defs_printer : printer
  
end

