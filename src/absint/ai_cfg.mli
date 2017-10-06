open Domain

module Make(S:sig
    val env: Env.env
    val pmod: Pmodule.pmodule
    val widening: int
    module D: DOMAIN
  end): sig
  module Domain : Domain.TERM_DOMAIN

  type control_point
  type domain = Domain.t
  type cfg
  type context

  val domain_manager: context -> Domain.man

  val empty_context : unit -> context

  val start_cfg: Expr.rsymbol -> cfg

  val put_expr_in_cfg: cfg -> context -> ?ret:Term.vsymbol option -> Expr.expr -> (control_point * control_point * ((control_point * Ity.xsymbol) list))

  val put_expr_with_pre: cfg -> context -> Expr.expr -> Term.term list -> (control_point * control_point * ((control_point * Ity.xsymbol) list))
  
  val eval_fixpoints: cfg -> context -> (Expr.expr * domain) list

  val domain_to_term: cfg -> context -> domain -> Term.term

  val add_variable: cfg -> context -> Ity.pvsymbol -> unit



end
