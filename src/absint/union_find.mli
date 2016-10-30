type t
type set
val empty: set
val is_leq: set -> set -> bool
val union: t -> t -> set -> set
val join: set -> set -> set
val new_class: unit -> t
val forget: t -> set -> t option * set
val print: set -> unit
val fold_equal: ('a -> t -> t -> 'a) -> 'a -> set -> 'a
