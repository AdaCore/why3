open Domain

module Make(S:sig
    module A:DOMAIN
    val env: Env.env
    val pmod: Pmodule.pmodule
  end) : TERM_DOMAIN
