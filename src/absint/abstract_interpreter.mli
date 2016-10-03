module Abstract_interpreter(S:sig
    val env: Env.env
    val pmod: Pmodule.pmodule
  end): sig
  type control_point
  type domain
  type cfg
  type local_ty

  val empty_local_ty : local_ty

  val start_cfg: Expr.rsymbol -> cfg

  val put_expr_in_cfg: cfg -> local_ty -> Expr.expr -> (control_point * control_point)

  val eval_fixpoints: cfg -> (Expr.expr * domain) list

  val domain_to_term: cfg -> domain -> Term.term

  val add_variable: cfg -> Ity.pvsymbol -> unit

end
