
type printer = Format.formatter -> unit

open Macrogen_decls

module type Decls = sig
  
  val dm : internal_decl
  val indent : int
  
end

module type Parameters = sig
  
  include Decls
  
  val variable_name : TName.t -> printer
  val size_name : TName.t -> printer
  val nat_size_name : TName.t -> printer
  val size_lemma_name : TName.t -> printer
  val slift_name : TName.t -> printer
  val rename_subst_name : TName.t -> printer
  val subst_compose_name : TName.t -> printer
  val renaming_composition_lemma_name : TName.t -> printer
  val rename_then_subst_composition_lemma_name : TName.t -> printer
  val subst_then_rename_composition_lemma_name : TName.t -> printer
  val subst_composition_lemma_name : TName.t -> printer
  val renaming_identity_lemma_name : TName.t -> printer
  val subst_identity_lemma_name : TName.t -> printer
  val associativity_lemma_name : bool * bool * bool -> TName.t -> printer
  val slift_composition_lemma_name : bool * bool -> TName.t -> printer
  val subst_identity_name : TName.t -> printer
  val slift_identity_lemma_name : TName.t -> printer
  val subst_of_rename_name : TName.t -> printer
  (* rename_subst s id = s *)
  val right_rename_by_identity_lemma_name : TName.t -> printer
  (* subst_compose s sid = s *)
  val right_subst_by_identity_lemma_name : TName.t -> printer
  (* rename_subst sid r = subst_of_rename r *)
  val left_rename_identity_lemma_name : TName.t -> printer
  (* subst_compose sid s = s *)
  val left_subst_identity_lemma_name : TName.t -> printer
  val rename_name : TName.t -> printer
  val subst_name : TName.t -> printer
  val free_var_predicate_name : TName.t -> TName.t -> printer
  val subst_free_var_inversion_helper_name :
    bool -> TName.t -> TName.t -> printer
  val subst_free_var_inversion_lemma_name :
    bool -> TName.t -> TName.t -> printer
  val rename_free_var_propagation_lemma_name : TName.t -> TName.t -> printer
  val subst_free_var_propagation_lemma_name :
    TName.t -> TName.t -> TName.t -> printer
  val free_var_equivalence_lemma_name : bool -> bool -> TName.t -> printer
  val close_name : TName.t -> TName.t -> printer
  val openv_name : TName.t -> TName.t -> printer
  val opent_name : TName.t -> TName.t -> printer
  val size_preservation_lemma_name : TName.t -> printer
  
end

