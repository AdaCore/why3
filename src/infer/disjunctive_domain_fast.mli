open Domain

type 'a a = private {t: 'a list; c: bool; i: int; }

module Make(A:DOMAIN): DOMAIN with type t = A.t a
