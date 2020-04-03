open Term


(* Bidirectional map between term and t *)

module Make : functor (S:sig type t end) -> sig
  type t
  val empty: t
  val add: t -> term -> S.t -> t
  val remove_term: t -> term -> t
  val remove_t: t -> S.t -> t
  val to_term: t -> S.t -> term
  val to_t: t -> term -> S.t
  val choose: t -> term * S.t
  val union: t -> t
    -> (S.t -> S.t -> term -> unit)
    -> (term -> term -> S.t -> unit)
    -> t
  val card: t -> int
end
