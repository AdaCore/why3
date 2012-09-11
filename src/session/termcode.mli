(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

val current_shape_version : int

type checksum
val print_checksum: Format.formatter -> checksum -> unit
val string_of_checksum: checksum -> string
val checksum_of_string: string -> checksum
val equal_checksum: checksum -> checksum -> bool
val dumb_checksum: checksum

type shape
val print_shape: Format.formatter -> shape -> unit
val string_of_shape: shape -> string
val shape_of_string: string -> shape

(*
val t_dist : term -> term -> float
  (** returns an heuristic distance between the two given terms. The
      result is always between 0.0 and 1.0. It is guaranteed that if
      the result is 0.0 then the terms are equal modulo alpha *)
*)


(*

  [t_shape t] provides a traversal of the term structure, generally
  in the order root-left-right, except for nodes Tquant and Tbin
  which are traversed in the order right-root-left, so that in "A ->
  B" we see B first, and if "Forall x,A" we see A first

*)


val t_shape_buf : ?version:int -> Term.term -> shape
  (** returns a shape of the given term *)

(*
val t_shape_list : Term.term -> string list
  (** returns a shape of the given term *)

val pr_shape_list : Format.formatter -> Term.term -> unit
*)

val task_checksum : ?version:int -> Task.task -> checksum


(** Pairing using shape and checksum *)

module type S = sig
  type t
  val checksum : t -> checksum
  val shape    : t -> shape
  val name     : t -> Ident.ident
end

module AssoMake (Old : S) (New : S) : sig
  val associate : Old.t list -> New.t list -> (New.t * Old.t option *bool) list
    (** associate the new things {New.t} to old things {Old.t}.
        (n,o,b) means if [o,b] is:
        - [Some o, true] the old thing [o] have the same checksum that the new
          thing [n].
        - [Some o, false] no old things have the same checksum
        than [n]. The new thing [o] has a shape similar to [n]
        - [None]  no old thing were similar enough. *)
end
