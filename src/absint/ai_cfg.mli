open Domain

module Make(S:sig
    val env: Env.env
    val pmod: Pmodule.pmodule
    module D: DOMAIN
  end): sig
  type control_point
  type domain
  type cfg
  type context

  val empty_context : context

  val start_cfg: Expr.rsymbol -> cfg

  val put_expr_in_cfg: cfg -> context -> Expr.expr -> (control_point * control_point * ((control_point * Ity.xsymbol) list))

  val put_expr_with_pre: cfg -> context -> Expr.expr -> Term.term list -> (control_point * control_point * ((control_point * Ity.xsymbol) list))
  
  val eval_fixpoints: cfg -> (Expr.expr * domain) list

  val domain_to_term: cfg -> domain -> Term.term

  val add_variable: cfg -> context -> Ity.pvsymbol -> context


end
