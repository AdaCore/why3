val string : Format.formatter -> string -> unit
val int : Format.formatter -> int -> unit
val bool : Format.formatter -> bool -> unit

val list :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit

val print_json_field :
  string -> (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit
