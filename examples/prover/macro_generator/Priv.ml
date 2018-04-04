
module type S = sig
  type base
  type t = private base
  val make : base -> t
  val destruct : t -> base
end

module Make = functor (X:sig type t end) -> struct
  type base = X.t
  type t = base
  let make x = x
  let destruct x = x
end

