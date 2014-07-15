
let compression_supported = false

module type S = sig 

type out_channel

val open_out: string -> out_channel

val output_char: out_channel -> char -> unit

val output: out_channel -> string -> int -> int -> unit

val output_string: out_channel -> string -> unit

val close_out: out_channel -> unit

type in_channel

val open_in: string -> in_channel

val input: in_channel -> string -> int -> int -> int

val really_input: in_channel -> string -> int -> int -> unit

val input_char: in_channel -> char

val close_in: in_channel -> unit

end

module Compress_none = Pervasives

module Compress_z = Pervasives
