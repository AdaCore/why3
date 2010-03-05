(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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


(* Tranformation on list of element with some memoisations *)

(* The type of transformation from list of 'a to list of 'b *)
type ('a,'b) t

(* compose two transformation, the underlying datastructures for
   the memoisation are shared *)
val compose : ('a,'b) t -> ('b,'c) t -> ('a,'c) t

(* apply a transformation and memoise *)
val apply : ('a,'b) t -> 'a list -> 'b list

(* clear the datastructures used to store the memoisation *)
val clear : ('a,'b) t -> unit

(* The signature of a module of transformation from elt1 to elt2*)
module type S =
sig
  (* The type of the elements of the list*)
  type t1
  type t2

  (* The general tranformation only one memoisation is performed with
     the argument given *)
  val all : (t1 list -> t2 list) -> (t1,t2) t

  (* map the element of the list from the first to the last.
     only one memoisation is performed *)
  val fold_map_right : ('a -> t1 -> ('a * t2 list)) -> 'a -> (t1,t2) t

  (* map the element of the list from the last to the first.
     A memoisation is performed at each step *)
  val fold_map_left : ('a -> t1 -> ('a * t2 list)) -> 'a -> (t1,t2) t

  (* map the element of the list without an environnment.
     A memoisation is performed at each step, and for each elements *)
  val elt : (t1 -> t2 list) -> (t1,t2) t

end

(* a type with a tag function  *)
type 'a tag

module type Sig =
  sig
    type t
    val tag : t tag
  end

open Theory
open Term

(* They are the only modules of signature S, we can have *)
module STerm : Sig with type t = term
module SFmla : Sig with type t = fmla
module SDecl : Sig with type t = decl
module STheory : Sig with type t = theory

(* The functor to construct transformation from one S.t to another *)
module Make (X1 : Sig)(X2 : Sig) : S with type t1 = X1.t with type t2 = X2.t

(* Predefined transformation *)
module TDecl : S with type t1 = decl and type t2 = decl
module TTheory : S with type t1 = theory and type t2 = theory
module TTheory_Decl : S with type t1 = theory and type t2 = decl
