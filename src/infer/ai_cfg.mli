open Domain
open Term
open Expr
open Ity

module type AiCfg = sig
  module QDom : Domain.TERM_DOMAIN

  type control_point
  type domain
  type cfg
  type context

  val domain_manager : context -> QDom.man
  val empty_context  : unit -> context
  val start_cfg      : unit -> cfg

  type xcontrol_point = control_point * xsymbol
  type control_points = control_point * control_point * xcontrol_point list

  val put_expr_in_cfg   : cfg -> context -> ?ret:vsymbol option -> expr ->
                         control_points
  val put_expr_with_pre : cfg -> context -> expr -> term list ->
                         control_points

  val eval_fixpoints : cfg -> context -> (expr * domain) list

  val domain_to_term : cfg -> context -> domain -> term

  val add_variable   : cfg -> context -> pvsymbol -> unit
end

module Make(S:sig
  val env       : Env.env
  val th_known  : Decl.known_map
  val mod_known : Pdecl.known_map
  val widening  : int
end)(Domain : DOMAIN): AiCfg
