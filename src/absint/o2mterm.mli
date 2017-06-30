module Make : functor (S:sig type t end) -> sig
  type t
  val empty: t
  val add: t -> Term.term -> S.t -> t
  val remove_term: t -> Term.term -> t
  val remove_t: t -> S.t -> t
  val to_term: t -> S.t -> Term.term
  val to_t: t -> Term.term -> S.t
  val union: t -> t -> t
  val card: t -> int
end
