open Domain

module Make(A:DOMAIN): DOMAIN with type t = A.t list (* domains should never be accessed directly, only useful for testing purpose *) and type man = A.man
