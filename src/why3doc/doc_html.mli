
open Format
open Why
open Theory

val print_theory : formatter -> theory -> unit

val print_header : formatter -> ?title:string -> ?css:string -> unit -> unit
val print_footer : formatter -> unit -> unit

val style_css : string -> unit
  (* write a default CSS in the given file *)
