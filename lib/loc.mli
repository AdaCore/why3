
open Format

(*s Line number for an absolute position *)

val report_line : formatter -> Lexing.position -> unit

(* Lexing positions *)

type position = Lexing.position * Lexing.position

exception Located of position * exn

val string : position -> string
val parse : string -> position

val dummy_position : position

type floc = string * int * int * int

val dummy_floc : floc

val extract :  position -> floc
val gen_report_line : formatter -> floc -> unit
val gen_report_position : formatter -> position -> unit
val report_position : formatter -> position -> unit
val report_obligation_position : ?onlybasename:bool -> formatter -> floc -> unit


(* for both type [t] and [position] *)

val join : 'a * 'b -> 'a * 'b -> 'a * 'b

val current_offset : int ref
val reloc : Lexing.position -> Lexing.position

(* Identifiers localization *)

val add_ident : string -> floc -> unit
val ident : string -> floc
