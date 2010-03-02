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

module type S =
sig
  (* The type of the elements of the list*)
  type elt1
  type elt2

  (* The general tranformation only one memoisation is performed with
     the argument given *)
  val all : (elt1 list -> elt2 list) -> (elt1,elt2) t

  (* map the element of the list from the first to the last.
     only one memoisation is performed *)
  val fold_map_right : ('a -> elt1 -> ('a * elt2 list)) -> 'a -> (elt1,elt2) t

  (* map the element of the list from the last to the first.
     A memoisation is performed at each step *)
  val fold_map_left : ('a -> elt1 -> ('a * elt2 list)) -> 'a -> (elt1,elt2) t

  (* map the element of the list without an environnment.
     A memoisation is performed at each step, and for each elements *)
  val elt : (elt1 -> elt2 list) -> (elt1,elt2) t
    
end

open Theory

module TDecl : S with type elt1 = decl and type elt2 = decl
module TDecl_or_Use : S with type elt1 = decl_or_use and type elt2 = decl_or_use
module TTheory : S with type elt1 = theory and type elt2 = theory
module TTheory_Decl : S with type elt1 = theory and type elt2 = decl


