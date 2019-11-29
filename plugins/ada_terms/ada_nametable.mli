
open Why3

val get_naming_table: unit -> Trans.naming_table
val set_naming_table: Trans.naming_table -> unit

val convert_array: Trans.naming_table -> string -> string
