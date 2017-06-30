module Make : functor (S:sig type t end) -> sig
  type t
  val empty: t
  val add: t -> Term.term -> S.t -> t
  val remove_term: t -> Term.term -> t
  val remove_t: t -> S.t -> t
  val to_term: t -> S.t -> Term.term
  val to_terms: t -> S.t -> unit Term.Mterm.t
  val to_t: t -> Term.term -> S.t
  val union: (S.t -> S.t -> unit) -> (Term.term -> unit) -> t -> t -> t
  val card: t -> int
  val get_inconsistent: t -> t -> Term.term list
  val filter_term: t -> (Term.term -> bool) -> t * S.t list
end
