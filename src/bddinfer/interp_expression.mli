
(** {1 Translation between expressions and abstract states} *)

val time_in_meet_condition : float ref

val meet_condition :
  old:Abstract.why_env -> Abstract.t -> Ast.condition -> Abstract.t
(** reduce the given state to the subset satisfying the given condition *)

val abstract_state_to_conditions : Abstract.t -> Ast.condition list
(** convert the given state to a set of conditions *)
