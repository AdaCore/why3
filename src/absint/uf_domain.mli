open Domain

val infer_debug : Debug.flag

module Make(S:sig
    module A:DOMAIN
    val env: Env.env
    val pmod: Pmodule.pmodule
  end) : TERM_DOMAIN
