Declare ML Module "whytac".
Require Export ZArith.
Open Scope Z_scope.
Require Export List.

Ltac ae := why "alt-ergo".
Ltac z3 := why "z3".
Ltac spass := why "spass".

(* type definitions *)

Definition t := list.

Inductive foo : Set :=
  C : t nat -> foo.

Goal forall x:foo, x=x.
intros.
ae.
Qed.

(* predicate definition *)

Definition p (x:nat) := x=O.

Goal p O.
ae.
Qed.

Definition eq (A:Set) (x y : A) := x=y.

Goal eq nat O O.
ae.
(*
why "z3".  (* BUG encoding decorate ici ? *)
Qed.
*)
Admitted.

Definition pred (n:nat) := match n with 
  | O => O
  | S p => p
  end.

Goal pred (S O) = O.
ae.
Admitted.

(* function definition *)

Definition f (x:Z) (y:Z) := x+y.

Goal f 1 2 = 3.
ae.
Qed.

Definition id A (x:A) := x.

Goal id nat O = O.
ae.
Qed.

(* inductive types *)

Parameter P : (nat -> nat) -> Prop.

Goal forall (a:Set), forall x:nat, x=S O -> P S -> 
  let y := (S (S O)) in S x=y.
intros.
ae.
Qed.

Goal  forall (a:Set), forall x:Z, x=1 -> P S -> let y := 2 in x+1=y.
intros.
ae.
Qed.

Goal  forall x: list nat, x=x.
intros.
ae.
Qed.

Goal forall x, (match x with (S (S _)) => True | _ => False end).
(* BUG *)
Admitted.


Goal forall a, forall (x: list (list a)), match x with nil => 1 | x :: r => 2 end <= 2.
intros.
try ae.
Admitted.


(* Mutually inductive types *)

Inductive tree : Set :=
  | Leaf : tree
  | Node : Z -> forest -> tree

with forest : Set :=
  | Nil : forest
  | Cons : tree -> forest -> forest.

Goal forall x : tree, x=x.
ae.
Qed.

Goal (match Leaf with Leaf => 1 | Node z f => 2 end)=1.
ae.
Qed.

(* Polymorphic, Mutually inductive types *)

Inductive ptree (a:Set) : Set :=
  | PLeaf : ptree a
  | PNode : a -> pforest a -> ptree a

with pforest (a:Set) : Set :=
  | PNil : pforest a
  | PCons : ptree a -> pforest a -> pforest a.

Goal forall x : ptree Z, x=x.
spass.
Qed.

(* the same, without parameters *)

Inductive ptree' : Type -> Type :=
  | PLeaf' : forall (a:Type), ptree' a
  | PNode' : forall (a:Type), a -> pforest' a -> ptree' a

with pforest' : Type -> Type :=
  | PNil' : forall  (a:Type), pforest' a
  | PCons' : forall (a:Type), ptree' a -> pforest' a -> pforest' a.

Goal forall x : ptree' Z, x=x.
spass.
Qed.

