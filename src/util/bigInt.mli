

type t

val compare : t -> t -> int

(** constants *)
val zero : t
val of_int : int -> t

(** basic operations *)
val succ : t -> t
val pred : t -> t
val add_int : int -> t -> t
val mul_int : int -> t -> t
val add : t -> t -> t
val sub : t -> t -> t
val mul : t -> t -> t
val minus : t -> t
val sign : t -> int

(** comparisons *)
val eq : t -> t -> bool
val lt : t -> t -> bool
val gt : t -> t -> bool
val le : t -> t -> bool
val ge : t -> t -> bool

(** Division and modulo operators with the convention 
that modulo is always non-negative.

It implies that division rounds down when divisor is positive, and
rounds up when divisor is negative.
*)
val euclidean_div_mod : t -> t -> t * t
val euclidean_div : t -> t -> t 
val euclidean_mod : t -> t -> t 

(** "computer" division, i.e division rounds towards zero, and thus [mod
    x y] has the same sign as x
*)
val computer_div_mod : t -> t -> t * t
val computer_div : t -> t -> t 
val computer_mod : t -> t -> t 

(** min and max *)
val min : t -> t -> t
val max : t -> t -> t

(** power of small integers. Second arg must be non-negative *)
val pow_int_pos : int -> int -> t

(** conversion with strings *)
val of_string : string -> t
val to_string : t -> string
