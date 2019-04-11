(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

#13 "src/session/compress_none.ml"
let compression_supported = false

module type S = sig

type out_channel

val open_out: string -> out_channel

val output_char: out_channel -> char -> unit

val output_substring: out_channel -> string -> int -> int -> unit

val output_string: out_channel -> string -> unit

val close_out: out_channel -> unit

type in_channel

val open_in: string -> in_channel

val input: in_channel -> bytes -> int -> int -> int

val really_input: in_channel -> bytes -> int -> int -> unit

val input_char: in_channel -> char

val close_in: in_channel -> unit

end

module Compress_none = Pervasives

module Compress_z = Pervasives
