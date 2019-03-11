(* TODO This wrapper should eventually be removed !
   For documentation refer to the mlmpfr documentation.
*)

(* Wrapper for mlMPFR:
   MPFR installed -> implemented with mlMPFR
   MPFR not installed -> dummy implementation
*)

type mpfr_float

(* Exception to be raised if mpfr is not installed *)
exception Not_Implemented

val set_emin: int -> unit
val set_emax: int -> unit
val set_default_prec: int -> unit

type mpfr_rnd_t =
  | To_Nearest
  | Toward_Zero
  | Toward_Plus_Infinity
  | Toward_Minus_Infinity
  | Away_From_Zero
  | Faithful

type sign = Positive | Negative

(* Elementary operations *)
val add: ?rnd:mpfr_rnd_t -> ?prec:int -> mpfr_float -> mpfr_float -> mpfr_float
val neg: ?rnd:mpfr_rnd_t -> ?prec:int -> mpfr_float -> mpfr_float
val mul: ?rnd:mpfr_rnd_t -> ?prec:int -> mpfr_float -> mpfr_float -> mpfr_float
val div: ?rnd:mpfr_rnd_t -> ?prec:int -> mpfr_float -> mpfr_float -> mpfr_float
val sqrt: ?rnd:mpfr_rnd_t -> ?prec:int -> mpfr_float -> mpfr_float
val sub: ?rnd:mpfr_rnd_t -> ?prec:int -> mpfr_float -> mpfr_float -> mpfr_float
val abs: ?rnd:mpfr_rnd_t -> ?prec:int -> mpfr_float -> mpfr_float
val fma: ?rnd:mpfr_rnd_t -> ?prec:int -> mpfr_float -> mpfr_float -> mpfr_float -> mpfr_float
val rint: ?rnd:mpfr_rnd_t -> ?prec:int -> mpfr_float -> mpfr_float


val min: ?rnd:mpfr_rnd_t -> ?prec:int -> mpfr_float -> mpfr_float -> mpfr_float
val max: ?rnd:mpfr_rnd_t -> ?prec:int -> mpfr_float -> mpfr_float -> mpfr_float

val signbit: mpfr_float -> sign

val subnormalize : ?rnd:mpfr_rnd_t -> mpfr_float -> mpfr_float


val make_from_str: ?prec:int -> ?rnd:mpfr_rnd_t -> ?base:int -> string -> mpfr_float
val make_from_int: ?prec:int -> ?rnd:mpfr_rnd_t -> int -> mpfr_float
val make_zero: ?prec:int -> sign -> mpfr_float

val get_formatted_str : ?rnd:mpfr_rnd_t -> ?base:int -> ?size:int -> mpfr_float -> string

(* Comparison functions *)

val greater_p : mpfr_float -> mpfr_float -> bool
val greaterequal_p : mpfr_float -> mpfr_float -> bool
val less_p : mpfr_float -> mpfr_float -> bool
val lessequal_p : mpfr_float -> mpfr_float -> bool
val equal_p : mpfr_float -> mpfr_float -> bool
val lessgreater_p : mpfr_float -> mpfr_float -> bool

val zero_p: mpfr_float -> bool
val nan_p : mpfr_float -> bool
val inf_p : mpfr_float -> bool

(* Constants *)
val const_pi: ?rnd:mpfr_rnd_t -> int -> mpfr_float
