module Make(S:sig
    val env: Env.env
    val widening: int
    module D: Domain.DOMAIN
  end): sig
  val infer_loop_invariants: Pmodule.pmodule -> Pmodule.pmodule
end
