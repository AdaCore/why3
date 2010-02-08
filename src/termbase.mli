type node = private
  | BVar of int * int
  | Var of Name.t
  | Tuple of t * t
  | App of t * t
  | Lam of Ty.t * varbind
  | Case of t * case
and t = private { tag : int ; node : node }
and varbind
and pattern = private
  | PBVar of int
  | PVar of Name.t
  | PTuple of pattern * pattern
  | Wildcard
and case

type decl = 
  | Logic of Name.t * Ty.scheme
  | Formula of poly_term
and poly_term

(** smart constructors *)
val lam : Name.t -> Ty.t -> t -> t
val app : t -> t -> t
val tuple : t -> t -> t
val var : Name.t -> t
val equal : t -> t -> bool
val alpha_equal : t -> t -> bool
val case : t -> pattern -> Name.t list -> t -> t

val open_case : case -> pattern * Name.t list * t
val close_case : pattern -> Name.t list -> t -> case

val unsafe_map : 
  tyfun:(Ty.t -> Ty.t) ->
  termfun:(t -> t) -> t -> t
(** [unsafe_map f t] recursively descends into [t] and then applies [f]
   everywhere going up; This function is unsafe in the sense that you might
   encounter [BVar] constructors. Only use it for simple rewriting that does not
   affect names, or does only affect global variables *)

val print : Format.formatter -> t -> unit

val wildcard : pattern
val pvar : Name.t -> pattern
val ptuple : pattern -> pattern -> pattern

val open_polyterm : poly_term -> Name.t list * t
val close_polyterm : Name.t list -> t -> poly_term

val open_lam : varbind -> Name.t * t
