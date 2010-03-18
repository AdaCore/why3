
module Dynlink :
  sig
    val is_native_not_defined : bool
    val is_native : bool
    val loadfile_private : string -> unit

    type error
    exception Error of error
    val error_message : error -> string
  end
