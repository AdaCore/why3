
open Macrogen_params
open Macrogen_decls
open Macrogen_printing

module Printer : functor (P:PrintParameters) -> sig
  
  val type_defs_printer : printer
  val size_defs_printer : printer
  val size_lemma_printer : printer
  val subst_defs_printer : bool -> printer
  val composition_lemma_printer : bool -> bool -> printer
  val identity_lemma_printer : bool -> printer
  val subst_composition_def_printer : bool -> printer
  val associativity_lemma_printer : bool * bool * bool -> printer
  val right_identity_lemma_printer : bool -> printer
  val left_identity_lemma_printer : bool -> printer
  val subst_lifting_printer : printer
  val lifting_composition_lemma_printer : (bool * bool) -> printer
  val subst_identity_printer : printer
  val free_var_def_printer : printer
  val subst_free_var_inversion_printer : bool -> printer
  val rename_free_var_propagation_lemma_printer : printer
  val subst_free_var_propagation_lemma_printer : printer
  val free_var_equivalence_lemma_printer : bool -> printer
  val free_var_derive_equivalence_lemma_printer : bool -> printer
  val open_close_defs_printer : printer
  val size_preservation_lemma_printer : printer
  
  val required_imports : printer
  val base_defs_printer : printer
  val subst_lemmae_defs_printer : printer
  val free_var_lemmae_defs_printer : printer
  
end

