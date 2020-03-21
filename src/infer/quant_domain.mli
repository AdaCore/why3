open Domain

module Make(S:sig
    module    Dom : TERM_DOMAIN
    val       env : Env.env
    val  th_known : Decl.known_map
    val mod_known : Pdecl.known_map
  end) : TERM_DOMAIN
