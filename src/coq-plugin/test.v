Declare ML Module "whytac".
Require Export ZArith.
Open Scope Z_scope.
Require Export List.

(* type definitions *)

Definition t := list.

Inductive foo : Set :=
  C : t nat -> foo.

Goal forall x:foo, x=x.
intros.
why.
Qed.

(* predicate definition *)

Definition p (x:nat) := x=O.

Goal p O.
why.
Qed.


(* function definition *)

Definition f (x:Z) (y:Z) := x+y.

Goal f 1 2 = 3.
why.
Qed.

Definition id A (x:A) := x.

Goal id nat O = O.
why.

Parameter P : (nat -> nat) -> Prop.

Goal forall (a:Set), forall x:nat, x=S O -> P S -> 
  let y := (S (S O)) in S x=y.
intros.
why.
Qed.

Goal  forall (a:Set), forall x:Z, x=1 -> P S -> let y := 2 in x+1=y.
intros.
why.
Qed.

(* Inductive types *)

Goal  forall x: list nat, x=x.
intros.
why.
Qed.

(* Mutually inductive types *)

Inductive tree : Set :=
  | Leaf : tree
  | Node : Z -> forest -> tree

with forest : Set :=
  | Nil : forest
  | Cons : tree -> forest -> forest.

Goal forall x : tree, x=x.
why.
Qed.

(* Polymorphic, Mutually inductive types *)

Inductive ptree (a:Set) : Set :=
  | PLeaf : ptree a
  | PNode : a -> pforest a -> ptree a

with pforest (a:Set) : Set :=
  | PNil : pforest a
  | PCons : ptree a -> pforest a -> pforest a.

Goal forall x : ptree Z, x=x.
why.
Qed.

(* the same, without parameters *)

Inductive ptree' : Type -> Type :=
  | PLeaf' : forall (a:Type), ptree' a
  | PNode' : forall (a:Type), a -> pforest' a -> ptree' a

with pforest' : Type -> Type :=
  | PNil' : forall  (a:Type), pforest' a
  | PCons' : forall (a:Type), ptree' a -> pforest' a -> pforest' a.

Goal forall x : ptree' Z, x=x.
why.
Qed.

