module Make(S:sig
    val env: Env.env
    module D: Domain.DOMAIN
  end): sig
  val infer_loop_invariants: Pmodule.pmodule -> Pmodule.pmodule
end
