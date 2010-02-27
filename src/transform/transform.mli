(* Tranformation on list of element with some memoisations *)

(* The functors need a type with a tag function *)
module type Sig =
sig
  type t

  (* return an unique int for each element of t *)
  val tag : t -> int
end

module type S =
sig
  (* The type of the elements of the list*)
  type elt

  (* The type of the transformations on list of elt *)
  type t

  (* The general tranformation only one memoisation is performed with
     the argument given *)
  val all : (elt list -> elt list) -> t

  (* map the element of the list from the first to the last.
     only one memoisation is performed *)
  val fold_map_right : ('a -> elt -> ('a * elt list)) -> 'a -> t

  (* map the element of the list from the last to the first.
     A memoisation is performed at each step *)
  val fold_map_left : ('a -> elt -> ('a * elt list)) -> 'a -> t

  (* map the element of the list without an environnment.
     A memoisation is performed at each step, and for each elements *)
  val elt : (elt -> elt list) -> t
    
  (* compose two transformation, the underliying datastructures for
     the memoisation are shared *)
  val compose : t -> t -> t
    
  (* apply a transformation and memoise *)
  val apply : t -> elt list -> elt list
    
  (* clear the datastructures used to store the memoisation *)
  val clear : t -> unit

end

module Make : functor (X : Sig) -> S with type elt = X.t


module TDecl : S with type elt = Theory.decl
module TDecl_or_Use : S with type elt = Theory.decl_or_use
