
module type S = sig
  type base
  type t = private base
  val make : base -> t
  val destruct : t -> base
end

module Make : functor (X:sig type t end) -> S with type base = X.t

