open Domain

module Make(S:sig
    module A:TERM_DOMAIN
    val env: Env.env
    val pmod: Pmodule.pmodule
  end) : TERM_DOMAIN
