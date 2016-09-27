module Abstract_interpreter(S:sig val env: Env.env end): sig
  type control_point
  type domain
  type cfg

  val start_cfg: Expr.rsymbol -> cfg

  val put_expr_in_cfg: cfg -> Expr.expr -> (control_point * control_point)

  val eval_fixpoints: cfg -> unit

  val get_domain: cfg -> control_point -> domain

  val domain_to_string: domain -> string

  val add_variable: cfg -> Ity.pvsymbol -> unit
end
