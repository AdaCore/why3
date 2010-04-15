Declare ML Module "whytac".
Require Export ZArith.
Open Scope Z_scope.
Require Export List.


Parameter P : (nat -> nat) -> Prop.

Goal forall (a:Set), forall x:nat, x=S O -> P S -> 
  let y := (S (S O)) in S x=y.
intros.
why.

Goal  forall (a:Set), forall x:Z, x=1 -> P S -> let y := 2 in x+1=y.
intros.
why.

(* Inductive types *)

Goal  forall x: list nat, x=x.
intros.

why.

(* Mutually inductive types *)

Inductive tree : Set :=
  | Leaf : tree
  | Node : Z -> forest -> tree

with forest : Set :=
  | Nil : forest
  | Cons : tree -> forest -> forest.

Goal forall x : tree, x=x.

(* Polymorphic, Mutually inductive types *)

Inductive ptree (a:Set) : Set :=
  | PLeaf : ptree a
  | PNode : a -> pforest a -> ptree a

with pforest (a:Set) : Set :=
  | PNil : pforest a
  | PCons : ptree a -> pforest a -> pforest a.

Goal forall x : ptree Z, x=x.

(* the same, without parameters *)

Inductive ptree' : Type -> Type :=
  | PLeaf' : forall (a:Type), ptree' a
  | PNode' : forall (a:Type), a -> pforest' a -> ptree' a

with pforest' : Type -> Type :=
  | PNil' : forall  (a:Type), pforest' a
  | PCons' : forall (a:Type), ptree' a -> pforest' a -> pforest' a.

Goal forall x : ptree' Z, x=x.
why.
