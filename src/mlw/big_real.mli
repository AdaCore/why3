type real

(* Exception raised when intervals do not allow decision of a comparison
   function. For example, equality on non-singleton intervals. *)
exception Undetermined

val init: int -> int -> int -> unit

val print_real: Format.formatter -> real -> unit

val real_from_str: string -> real
val real_from_fraction: string -> string -> real

(* Real operations *)
val neg: real -> real
val add: real -> real -> real
val mul: real -> real -> real
val div: real -> real -> real
val sqrt: real -> real

(* Real comparisons *)
val eq: real -> real -> bool
val lt: real -> real -> bool
val le: real -> real -> bool

(* Constants *)
val pi: real
