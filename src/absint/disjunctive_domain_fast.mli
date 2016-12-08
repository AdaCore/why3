open Domain

type 'a a = private {t: 'a list; c: bool; i: int; }

module type D = sig
  include DOMAIN
  val round_integers: man -> env -> t -> t
end

module Make(A:DOMAIN): D with type t = A.t a
