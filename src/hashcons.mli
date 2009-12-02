(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
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

(*s Hash tables for hash consing. 

    Hash consed values are of the
    following type [hash_consed]. The field [tag] contains a unique
    integer (for values hash consed with the same table). The field
    [hkey] contains the hash key of the value (without modulo) for
    possible use in other hash tables (and internally when hash
    consing tables are resized). The field [node] contains the value
    itself. 

    Hash consing tables are using weak pointers, so that values that are no
    more referenced from anywhere else can be erased by the GC. *)

module type HashedType =
  sig
    type node
    val equal : node -> node -> bool
    val hash : node -> int

    type t
    val node : t -> node
  end

module type S =
  sig
    type node
    type t

    val hashcons : node -> (node -> int -> t) -> t
      (** [hashcons n f] hash-cons the value [n] using function [f] i.e. returns
	  any existing value in the table equal to [n], if any; 
	  otherwise, creates a new value with function [f], stores it
	  in the table and returns it. Function [f] is passed
	  the node [n] as first argument and the unique id as second argument.
      *)

    val iter : (t -> unit) -> unit
      (** [iter f] iterates [f] over all elements of the table . *)
    val stats : unit -> int * int * int * int * int * int
      (** Return statistics on the table.  The numbers are, in order:
	  table length, number of entries, sum of bucket lengths,
	  smallest bucket length, median bucket length, biggest 
	  bucket length. *)
  end

module Make(H : HashedType) : (S with type node = H.node and type t = H.t)
