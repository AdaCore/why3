(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*s This module provides a generic ASCII pretty-printing function for trees,
    in a way similar to what the Unix command pstree does:

bash-+-emacs-+-emacsserver
     |       `-ispell
     |-pstree
     `-xdvi.bin
*)

(*s A tree structure is given as an abstract type [t] together with a
    decomposition function [decomp] returning the label of the node and
    the list of the children trees. Leaves are nodes with no child (i.e.
    an empty list). *)

module type Tree = sig
  type t
  val decomp : t -> string * t list
end

(*s The functor [Make] takes a tree structure [T] as argument and provides a
    single function [print: formatter -> T.t -> unit] to print a tree on a
    given formatter. *)

module Make (T : Tree) : sig
  val print : Format.formatter -> T.t -> unit
end


(** With type variable *)
module type PTree = sig
  type 'a t
  val decomp : 'a t -> string * 'a t list
end

(*s The functor [Make] takes a tree structure [T] as argument and provides a
    single function [print: formatter -> T.t -> unit] to print a tree on a
    given formatter. *)

module PMake (T : PTree) : sig
  val print : Format.formatter -> 'a T.t -> unit
end
