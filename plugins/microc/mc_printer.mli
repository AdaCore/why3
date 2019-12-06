
open Why3

(* This function is used as an extension of printing of task for microc *)
val microc_ext_printer: (Format.formatter -> Pretty.any_pp -> unit) ->
  Format.formatter -> Pretty.any_pp -> unit
