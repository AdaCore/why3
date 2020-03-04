open Domain

val infer_debug : Debug.flag

module Make(S:sig
    module A:DOMAIN
    val env: Env.env
    val th_known: Decl.known_map
    val mod_known: Pdecl.known_map
  end) : TERM_DOMAIN
