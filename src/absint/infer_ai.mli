module type Abs_int_options = sig
  val env       : Env.env        (* Why3 environment *)
  val widening  : int            (* widening value for fixpoint *)
  module Domain : Domain.DOMAIN  (* abstract interpretation domain *)
end

module type Inv_gen = sig
  val infer_loop_invariants: Pmodule.pmodule -> Pmodule.pmodule
end

module Make (S: Abs_int_options) : Inv_gen
